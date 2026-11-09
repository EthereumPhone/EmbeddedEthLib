/* Plain C SHA-256 reference (FIPS 180-4), same harness shape as the Lean timing images. */
#include <stdint.h>
#include <stddef.h>
static const uint32_t K[64]={0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
#define R(x,n) (((x)>>(n))|((x)<<(32-(n))))
static void compress(uint32_t h[8], const uint8_t *m){uint32_t w[64],a,b,c,d,e,f,g,hh;
 for(int t=0;t<16;t++)w[t]=(uint32_t)m[4*t]<<24|(uint32_t)m[4*t+1]<<16|(uint32_t)m[4*t+2]<<8|m[4*t+3];
 for(int t=16;t<64;t++)w[t]=(R(w[t-2],17)^R(w[t-2],19)^(w[t-2]>>10))+w[t-7]+(R(w[t-15],7)^R(w[t-15],18)^(w[t-15]>>3))+w[t-16];
 a=h[0];b=h[1];c=h[2];d=h[3];e=h[4];f=h[5];g=h[6];hh=h[7];
 for(int t=0;t<64;t++){uint32_t t1=hh+(R(e,6)^R(e,11)^R(e,25))+((e&f)^(~e&g))+K[t]+w[t],t2=(R(a,2)^R(a,13)^R(a,22))+((a&b)^(a&c)^(b&c));hh=g;g=f;f=e;e=d+t1;d=c;c=b;b=a;a=t1+t2;}
 h[0]+=a;h[1]+=b;h[2]+=c;h[3]+=d;h[4]+=e;h[5]+=f;h[6]+=g;h[7]+=hh;}
static void sha256(const uint8_t *msg,size_t len,uint8_t out[32]){uint32_t h[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
 uint8_t blk[64];size_t i=0;for(;i+64<=len;i+=64)compress(h,msg+i);size_t r=len-i;for(size_t j=0;j<64;j++)blk[j]=0;for(size_t j=0;j<r;j++)blk[j]=msg[i+j];blk[r]=0x80;
 if(r>=56){compress(h,blk);for(size_t j=0;j<64;j++)blk[j]=0;} uint64_t bits=(uint64_t)len*8;for(int j=0;j<8;j++)blk[63-j]=(uint8_t)(bits>>(8*j));compress(h,blk);
 for(int j=0;j<8;j++){out[4*j]=h[j]>>24;out[4*j+1]=h[j]>>16;out[4*j+2]=h[j]>>8;out[4*j+3]=h[j];}}
static void sh(uint32_t op, void *arg){register uint32_t r0 __asm__("r0")=op;register void*r1 __asm__("r1")=arg;__asm__ volatile("bkpt 0xab":"+r"(r0):"r"(r1):"memory");}
static void pc(char c){sh(3,&c);}
void Reset_Handler(void){uint8_t acc=0,out[32],msg[3]; static volatile const uint8_t seed[3]={0x61,0x62,0x63}; msg[0]=seed[0];msg[1]=seed[1];
 for(int i=0;i<NHASH;i++){msg[2]=seed[2]+i;sha256(msg,3,out);acc^=out[0];}
 pc("0123456789abcdef"[acc>>4]);pc("0123456789abcdef"[acc&15]);pc('\n');uint32_t a[2]={0x20026,0};sh(0x18,a);for(;;){}}
