#include <stdio.h>
#include <time.h>
#include <stdlib.h>

typedef struct{
	int key;
	int val;
} str64;

long long NCmps;

int cmp64(const str64 *a,const str64 *b){
	NCmps++;
	if(a->key<b->key) return -1;
	if(a->key>b->key) return 1;
	return 0;
}

#define SORT_TYPE str64
#define SORT_CMP cmp64

#include"GrailSort.h"

/******** Tests *********/

int seed=100000001;
int rand(int k){
	seed=seed*1234565+1;
	return (int)(((long long)(seed&0x7fffffff)*k)>>31);
}


void GenArray(SORT_TYPE *arr,int *KeyCntr,int Len,int NKey){
	for(int i=0;i<NKey;i++) KeyCntr[i]=0;
	for(int i=0;i<Len;i++){
		if(NKey){
			int key=rand(NKey);
			arr[i].key=key;
			arr[i].val=KeyCntr[key]++;
		} else{
			arr[i].key=rand(1000000000);
			arr[i].val=0;
		}
	}
}

bool TestArray(SORT_TYPE *arr,int Len){
	for(int i=1;i<Len;i++){
		int dk=SORT_CMP(arr+(i-1),arr+i);
		if(dk>0) return false;
		if(dk==0 && arr[i-1].val>arr[i].val) return false;
	}
	return true;
}

void PrintArray(char *s,SORT_TYPE *arr,int Len){
	printf("%s:",s);
	for(int i=0;i<Len;i++) printf(" %d:%d",arr[i].key,arr[i].val);
	printf("\n");
}

extern "C" int xcmp(const void *a,const void *b){
	return SORT_CMP((const SORT_TYPE *)a,(const SORT_TYPE *)b);
}

void qtest(SORT_TYPE *arr,int Len){
	qsort(arr,Len,sizeof(SORT_TYPE),xcmp);
}

void Check(SORT_TYPE *arr,int *KeyCntr,int Len,int NKey,bool alg){
	GenArray(arr,KeyCntr,Len,NKey);
	printf("%s N: %d, NK: %d ",alg ? "GrailSort:   " : "InPlaceMerge:",Len,NKey);
	//PrintArray("Input",arr,Len);
	NCmps=0;
	long ct=clock();
	if(alg) GrailSort(arr,Len);
	else{
		RecStableSort(arr,Len);
		//qtest(arr,Len);
	}
	printf("Cmps: %I64d, time: %ld ms ",NCmps,clock()-ct);
	bool ok=TestArray(arr,Len);
	if(ok){
		printf("Ok\n");
	} else{
		printf("Fail\n");
	}
}



void main(){
	int NMax=100000000;
	int NMaxKey=100000;
	SORT_TYPE *A=new SORT_TYPE[NMax];
	int *Keys=new int[NMaxKey];

	/*
	Check(A,Keys,NMax,0,false);
	Check(A,Keys,NMax,0,true);
	*/
	for(int u=100;u<=NMax;u*=10){
		for(int v=2;v<=u && v<=NMaxKey;v*=2){
			Check(A,Keys,u,v-1,false);
			Check(A,Keys,u,v-1,true);
		}
	}
}
