#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>

typedef uint8_t	byte;
typedef uint32_t	u32;
typedef uint64_t	u64;
typedef uint32_t CWord;
typedef u32 tword;

typedef struct{
	u64 h;
	u64 l;
}u128; // state word

#define CRYPTO_KEYBYTES 16
#define CRYPTO_NSECBYTES 0
#define CRYPTO_NPUBBYTES 16
#define CRYPTO_ABYTES 16
#define CRYPTO_NOOVERLAP 1
#define CRYPTO_BYTES 64
#define RATE_INBITS 128
#define RATE_INBYTES ((RATE_INBITS + 7) / 8)

#define SQUEEZE_RATE_INBITS 128
#define SQUEEZE_RATE_INBYTES ((SQUEEZE_RATE_INBITS + 7) / 8)

#define CAPACITY_INBITS 128
#define CAPACITY_INBYTES ((CAPACITY_INBITS + 7) / 8)

#define STATE_INBITS (RATE_INBITS + CAPACITY_INBITS)
#define STATE_INBYTES ((STATE_INBITS + 7) / 8)

#define KEY_INBITS (CRYPTO_KEYBYTES * 8)
#define KEY_INBYTES (CRYPTO_KEYBYTES)

#define NOUNCE_INBITS (CRYPTO_NPUBBYTES * 8)
#define NOUNCE_INBYTES (CRYPTO_NPUBBYTES)

#define TAG_INBITS 128
#define TAG_INBYTES ((TAG_INBITS + 7) / 8)
#define LAST_THREE_BITS_OFFSET (STATE_INBITS - (STATE_INBYTES - 1) * 8 - 3)

#define TAG_MATCH	 0
#define TAG_UNMATCH	-1
#define OTHER_FAILURES -2

#define ENC 0
#define DEC 1
#define ROUND			12
#define min(x,y) ((x)<(y)?(x):(y))
#define max(x,y) ((x)>(y)?(x):(y))
#define D				8

// Definition of basic internal functions
static uint8_t selectConst(const bool condition1,const bool condition2,const uint8_t option1,const uint8_t option2,const uint8_t option3,const uint8_t option4)
{
	if (condition1 && condition2) return option1;
	if (condition1) return option2;
	if (condition2) return option3;
	return option4;
}

static void concatenate(uint8_t *out,const uint8_t *in_left, const size_t leftlen_inbytes,const uint8_t *in_right, const size_t rightlen_inbytes)
{
	memcpy(out, in_left, leftlen_inbytes);
	memcpy(out + leftlen_inbytes, in_right, rightlen_inbytes);
}

static void XOR(uint8_t *out,const uint8_t *in_left,const uint8_t *in_right,const size_t iolen_inbytes)
{
	size_t i;
	for (i = 0; i < iolen_inbytes; i++) out[i] = in_left[i] ^ in_right[i];
}

static void XOR_const(uint8_t *State_inout,const uint8_t  Constant)
{
	State_inout[STATE_INBYTES - 1] ^= (Constant << LAST_THREE_BITS_OFFSET);
}

static void ROTR1(uint8_t *out,const uint8_t *in,const size_t iolen_inbytes)
{
	uint8_t tmp = in[0];
	size_t i;
	for (i = 0; i < iolen_inbytes - 1; i++)
	{
		out[i] = (in[i] >> 1) | ((in[(i+1)] & 1) << 7);
	}
	out[iolen_inbytes - 1] = (in[i] >> 1) | ((tmp & 1) << 7);
}

static void ShuffleXOR(uint8_t *DataBlock_out,const uint8_t *OuterState_in,const uint8_t *DataBlock_in,const size_t DBlen_inbytes)
{
	const uint8_t *OuterState_part1 = OuterState_in;
	const uint8_t *OuterState_part2 = OuterState_in + RATE_INBYTES / 2;

	uint8_t OuterState_part1_ROTR1[RATE_INBYTES / 2] = { 0 };
	size_t i;

	ROTR1(OuterState_part1_ROTR1, OuterState_part1, RATE_INBYTES / 2);

	i = 0;
	while ((i < DBlen_inbytes) && (i < RATE_INBYTES / 2))
	{
		DataBlock_out[i] = OuterState_part2[i] ^ DataBlock_in[i];
		i++;
	}
	while (i < DBlen_inbytes)
	{
		DataBlock_out[i] = OuterState_part1_ROTR1[i - RATE_INBYTES / 2] ^ DataBlock_in[i];
		i++;
	}
}

static void rhoohr(uint8_t *OuterState_inout,uint8_t *DataBlock_out,const uint8_t *DataBlock_in,const size_t DBlen_inbytes,const uint32_t EncDecInd)
{
	ShuffleXOR(DataBlock_out, OuterState_inout, DataBlock_in, DBlen_inbytes);

	if (EncDecInd == ENC)
		XOR(OuterState_inout, OuterState_inout, DataBlock_in, DBlen_inbytes);
	else
		XOR(OuterState_inout, OuterState_inout, DataBlock_out, DBlen_inbytes);
}

static void HASH(uint8_t *State_inout,const uint8_t *Data_in,const uint64_t Dlen_inbytes,const uint8_t Constant)
{
	uint8_t *State = State_inout;
	size_t Dlen_inblocks = (Dlen_inbytes + RATE_INBYTES - 1) / RATE_INBYTES;
	size_t LastDBlocklen;
	size_t i;

	for (i = 0; i < Dlen_inblocks - 1; i++)
	{
		PHOTON_Permutation(State);
		XOR(State, State, Data_in + i * RATE_INBYTES, RATE_INBYTES);
	}
	PHOTON_Permutation(State);	
	LastDBlocklen = Dlen_inbytes - i * RATE_INBYTES;
	XOR(State, State, Data_in + i * RATE_INBYTES, LastDBlocklen);
	if (LastDBlocklen < RATE_INBYTES) State[LastDBlocklen] ^= 0x01; // ozs

	XOR_const(State, Constant);
}

static void ENCorDEC(uint8_t *State_inout,uint8_t *Data_out,const uint8_t *Data_in,const uint64_t Dlen_inbytes,const uint8_t Constant,const uint32_t EncDecInd)
{
	uint8_t *State = State_inout;
	size_t Dlen_inblocks = (Dlen_inbytes + RATE_INBYTES - 1) / RATE_INBYTES;
	size_t LastDBlocklen;
	size_t i;

	for (i = 0; i < Dlen_inblocks - 1; i++)
	{
		PHOTON_Permutation(State);
		rhoohr(State, Data_out + i * RATE_INBYTES, Data_in + i * RATE_INBYTES, RATE_INBYTES, EncDecInd);
	}
	PHOTON_Permutation(State);
	LastDBlocklen = Dlen_inbytes - i * RATE_INBYTES;
	rhoohr(State, Data_out + i * RATE_INBYTES, Data_in + i * RATE_INBYTES, LastDBlocklen, EncDecInd);
	if (LastDBlocklen < RATE_INBYTES) State[LastDBlocklen] ^= 0x01; // ozs

	XOR_const(State, Constant);
}

static void TAG(uint8_t *Tag_out,uint8_t *State)
{
	size_t i;

	i = TAG_INBYTES;
	while (i > SQUEEZE_RATE_INBYTES)
	{
		PHOTON_Permutation(State);
		memcpy(Tag_out, State, SQUEEZE_RATE_INBYTES);
		Tag_out += SQUEEZE_RATE_INBYTES;
		i -= SQUEEZE_RATE_INBYTES;
	}
	PHOTON_Permutation(State);
	memcpy(Tag_out, State, i);
}

int crypto_aead_encrypt(unsigned char *c, unsigned long long *clen,const unsigned char *m, unsigned long long mlen,const unsigned char *ad, unsigned long long adlen,
	const unsigned char *nsec,const unsigned char *npub,const unsigned char *k)
{

	uint8_t *C = c;
	uint8_t *T = c + mlen;
	const uint8_t *M = m;
	const uint8_t *A = ad;
	const uint8_t *N = npub;
	const uint8_t *K = k;

	uint8_t State[STATE_INBYTES] = { 0 };
	uint8_t c0;
	uint8_t c1;
	
	concatenate(State, N, NOUNCE_INBYTES, K, KEY_INBYTES);

	if ((adlen == 0) && (mlen == 0))
	{
		XOR_const(State, 1);
		TAG(T, State);
		*clen = TAG_INBYTES;
		return 0;
	}

	c0 = selectConst((mlen != 0), ((adlen % RATE_INBYTES) == 0), 1, 2, 3, 4);
	c1 = selectConst((adlen != 0), ((mlen % RATE_INBYTES) == 0), 1, 2, 5, 6);

	if (adlen != 0) HASH(State, A, adlen, c0);
	if ( mlen != 0) ENCorDEC(State, C, M, mlen, c1, ENC);
	
	TAG(T, State);
	*clen = mlen + TAG_INBYTES;
	return 0;
}

int crypto_aead_decrypt(unsigned char *m, unsigned long long *mlen,unsigned char *nsec,const unsigned char *c, unsigned long long clen,
	const unsigned char *ad, unsigned long long adlen,const unsigned char *npub,const unsigned char *k)
{
	uint8_t *M = NULL;
	const uint8_t *C = c;
	const uint8_t *T = c + clen - TAG_INBYTES;
	const uint8_t *A = ad;
	const uint8_t *N = npub;
	const uint8_t *K = k;

	uint8_t State[STATE_INBYTES] = { 0 };
	uint8_t T_tmp[TAG_INBYTES] = { 0 };
	uint8_t c0;
	uint8_t c1;
	uint64_t cmtlen;

	if (clen < TAG_INBYTES) return TAG_UNMATCH;
	cmtlen = clen - TAG_INBYTES;

	concatenate(State, N, NOUNCE_INBYTES, K, KEY_INBYTES);

	if ((adlen == 0) && (cmtlen == 0))
	{
		XOR_const(State, 1);
		TAG(T_tmp, State);
		if (memcmp(T_tmp, T, TAG_INBYTES) != 0) return TAG_UNMATCH;
		*mlen = 0;
		return TAG_MATCH;
	}

	c0 = selectConst((cmtlen != 0), ((adlen % RATE_INBYTES) == 0), 1, 2, 3, 4);
	c1 = selectConst((adlen != 0), ((cmtlen % RATE_INBYTES) == 0), 1, 2, 5, 6);

	if (adlen != 0) HASH(State, A, adlen, c0);
	if (cmtlen != 0)
	{
		M = (uint8_t *)malloc(cmtlen);
		if (M == NULL) return OTHER_FAILURES;
		ENCorDEC(State, M, C, cmtlen, c1, DEC);
	}

	TAG(T_tmp, State);
	if (memcmp(T_tmp, T, TAG_INBYTES) != 0)
	{
		if (M != NULL) free(M);
		return TAG_UNMATCH;
	}

	if (cmtlen != 0)
	{
		memcpy(m, M, cmtlen);
		free(M);
	}
	*mlen = cmtlen;
	return TAG_MATCH;
}

#define S				4
const byte ReductionPoly = 0x3;
const byte WORDFILTER = ((byte) 1<<S)-1;
int DEBUG = 0;
unsigned long long MessBitLen = 0;

const byte RC[D][12] = {
	{1, 3, 7, 14, 13, 11, 6, 12, 9, 2, 5, 10},
	{0, 2, 6, 15, 12, 10, 7, 13, 8, 3, 4, 11},
	{2, 0, 4, 13, 14, 8, 5, 15, 10, 1, 6, 9},
	{6, 4, 0, 9, 10, 12, 1, 11, 14, 5, 2, 13},
	{14, 12, 8, 1, 2, 4, 9, 3, 6, 13, 10, 5},
	{15, 13, 9, 0, 3, 5, 8, 2, 7, 12, 11, 4},
	{13, 15, 11, 2, 1, 7, 10, 0, 5, 14, 9, 6},
	{9, 11, 15, 6, 5, 3, 14, 4, 1, 10, 13, 2}
};

const byte MixColMatrix[D][D] = {
	{ 2,  4,  2, 11,  2,  8,  5,  6},
	{12,  9,  8, 13,  7,  7,  5,  2},
	{ 4,  4, 13, 13,  9,  4, 13,  9},
	{ 1,  6,  5,  1, 12, 13, 15, 14},
	{15, 12,  9, 13, 14,  5, 14, 13},
	{ 9, 14,  5, 15,  4, 12,  9,  6},
	{12,  2,  2, 10,  3,  1,  1, 14},
	{15,  1, 13, 10,  5, 10,  2,  3}
};

byte sbox[16] = {12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2};

byte FieldMult(byte a, byte b)
{
	byte x = a, ret = 0;
	int i;
	for(i = 0; i < S; i++) {
		if((b>>i)&1) ret ^= x;
		if((x>>(S-1))&1) {
			x <<= 1;
			x ^= ReductionPoly;
		}
		else x <<= 1;
	}
	return ret&WORDFILTER;
}

void PrintState(byte state[D][D])
{
	if(!DEBUG) return;
	int i, j;
	for(i = 0; i < D; i++){
		for(j = 0; j < D; j++)
			printf("%2X ", state[i][j]);
		printf("\n");
	}
	printf("\n");
}

void PrintState_Column(CWord state[D])
{
	if(!DEBUG) return;
	int i, j;
	for(i = 0; i < D; i++){
		for(j = 0; j < D; j++)
			printf("%2X ", (state[j]>>(i*S)) & WORDFILTER);
		printf("\n");
	}
	printf("\n");
}

void AddKey(byte state[D][D], int round)
{
	int i;
	for(i = 0; i < D; i++)
		state[i][0] ^= RC[i][round];
}

void SubCell(byte state[D][D])
{
	int i,j;
	for(i = 0; i < D; i++)
		for(j = 0; j <  D; j++)
			state[i][j] = sbox[state[i][j]];
}

void ShiftRow(byte state[D][D])
{
	int i, j;
	byte tmp[D];
	for(i = 1; i < D; i++) {
		for(j = 0; j < D; j++)
			tmp[j] = state[i][j];
		for(j = 0; j < D; j++)
			state[i][j] = tmp[(j+i)%D];
	}
}

void MixColumn(byte state[D][D])
{
	int i, j, k;
	byte tmp[D];
	for(j = 0; j < D; j++){
		for(i = 0; i < D; i++) {
			byte sum = 0;
			for(k = 0; k < D; k++)
				sum ^= FieldMult(MixColMatrix[i][k], state[k][j]);
			tmp[i] = sum;
		}
		for(i = 0; i < D; i++)
			state[i][j] = tmp[i];
	}
}

tword Table[D][1<<S];
void SCShRMCS(byte state[D][D])
{
	int c,r;
	tword v;
	byte os[D][D];
	memcpy(os, state, D*D);

	for(c = 0; c < D; c++){ // for all columns
		v = 0;
		for(r = 0; r < D; r++) // for all rows in this column i after ShiftRow
			v ^= Table[r][os[r][(r+c)%D]];

		for(r = 1; r <= D; r++){
			state[D-r][c] = (byte)v & WORDFILTER;
			v >>= S;
		}
	}
}

void Permutation(byte state[D][D], int R)
{
	int i;
	for(i = 0; i < R; i++) {
		if(DEBUG) printf("--- Round %d ---\n", i);
		AddKey(state, i); PrintState(state);
#ifndef _TABLE_
		SubCell(state); PrintState(state);
		ShiftRow(state); PrintState(state);
		MixColumn(state); 
#else
		SCShRMCS(state);
#endif
		PrintState(state);
	}
}

void PHOTON_Permutation(unsigned char *State_in)
{
    byte state[D][D];
    int i;

	for (i = 0; i < D * D; i++)
		state[i / D][i % D] = (State_in[i / 2] >> (4 * (i & 1))) & 0xf;
   
    Permutation(state, ROUND);
	memset(State_in, 0, (D * D) / 2);
	for (i = 0; i < D * D; i++)
		State_in[i / 2] |= (state[i / D][i % D] & 0xf) << (4 * (i & 1));
}

void hextobyte(char *hexstring, unsigned char *bytearray ) {
	int i;
	int str_len = strlen(hexstring);
	for (i = 0; i < (str_len / 2); i++)
		sscanf(hexstring + 2*i, "%02x", &bytearray[i]);
}

void string2hexString(unsigned char* input, int clen, char* output)
{
	int loop=0;
	int i=0;

	for (i=0;i<clen;i+=2){
		sprintf((char*)(output+i),"%02X", input[loop]);
		loop+=1;
	}
	//insert NULL at the end of the output string
	output[i++] = '\0';
}

int main (int argc, char *argv[]) {
	unsigned long long mlen;
	unsigned long long clen;
	unsigned char plaintext[CRYPTO_BYTES];
	unsigned char cipher[CRYPTO_BYTES]; 
	unsigned char npub[CRYPTO_NPUBBYTES]="";
	unsigned char ad[CRYPTO_ABYTES]="";
	unsigned char nsec[CRYPTO_ABYTES]="";
	unsigned char key[CRYPTO_KEYBYTES];

	char pl[CRYPTO_BYTES]="esra";
	char chex[CRYPTO_BYTES]="";
	char keyhex[2*CRYPTO_KEYBYTES+1]="0123456789ABCDEF0123456789ABCDEF";
	char nonce[2*CRYPTO_NPUBBYTES+1]="000000000000111111111111";
	char add[CRYPTO_ABYTES]="";

	if( argc > 1 )
		strcpy(pl,argv[1]);

	if( argc > 2 )
		strcpy(keyhex,argv[2]);

	if( argc > 3 )
		strcpy(nonce,argv[3]);

	if( argc > 4 )
		strcpy(add,argv[4]);

	if (strlen(keyhex)!=32) {
		printf("Key length needs to be 16 bytes");
		return(0);
	}

	strcpy(plaintext,pl);
	strcpy(ad,add);
	hextobyte(keyhex,key);
	hextobyte(nonce,npub);

	printf("\tPhoton-Beetle light-weight cipher\n");
	printf("Plaintext : %s\n",plaintext);
	printf("Key : %s\n",keyhex);
	printf("Nonce : %s\n",nonce);

	int ret = crypto_aead_encrypt(cipher,&clen,plaintext,strlen(plaintext),ad,strlen(ad),nsec,npub,key);
	string2hexString(cipher,clen,chex);

	printf("Cipher: %s, Len: %llu\n",chex, clen);

	ret = crypto_aead_decrypt(plaintext,&mlen,nsec,cipher,clen,ad,strlen(ad),npub,key);
	plaintext[mlen]='\0';
	printf("Plaintext: %s, Len: %llu\n",plaintext, mlen);

	if (ret==0)
		printf("DONE!\n");
	return 0;
}