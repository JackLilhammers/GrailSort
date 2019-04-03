#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <algorithm>

typedef struct
{
    int key;
    int val;
} str64;

long long NCmps;

int cmp64(const str64 *a, const str64 *b)
{
    NCmps++;
    if (a->key < b->key)
    {
        return -1;
    }
    if (a->key > b->key)
    {
        return 1;
    }
    return 0;
}

int new_cmp64(const void *__a, const void *__b)
{
    const str64 *a = (const str64 *)__a;
    const str64 *b = (const str64 *)__b;
    NCmps++;
    if (a->key < b->key)
    {
        return -1;
    }
    else if (a->key > b->key)
    {
        return 1;
    }
    else
    {
        return 0;
    }
}

#define SORT_TYPE str64
#define SORT_CMP cmp64
#define NEW_SORT_CMP new_cmp64

#include"GrailSort.h"

/******** Tests *********/

typedef enum eAlgorithm
{
    eStableSort,
    eGrailSort,
    eQSort,
    n_Algorithms
} eAlgorithm;
const char *alg_names[n_Algorithms] = {"StableSort", "GrailSort", "QSort"};

typedef enum eTestResult
{
    eOk,
    eUnstable,
    eFail,
    n_Results
} eTestResult;
const char *test_msgs[n_Results] = {"Ok", "Unstable", "Fail"};

int seed = 100000001;
int rand(int k)
{
    seed = seed * 1234565 + 1;
    return (int)(((long long)(seed & 0x7fffffff) * k) >> 31);
}


void GenArray(SORT_TYPE *arr, int *KeyCntr, int Len, int NKey)
{
    for (int i = 0; i < NKey; i++)
    {
        KeyCntr[i] = 0;
    }
    for (int i = 0; i < Len; i++)
    {
        if (NKey)
        {
            int key = rand(NKey);
            arr[i].key = key;
            arr[i].val = KeyCntr[key]++;
        }
        else
        {
            arr[i].key = rand(1000000000);
            arr[i].val = 0;
        }
    }
}

eTestResult TestArray(SORT_TYPE *arr, int Len)
{
    for (int i = 1; i < Len; i++)
    {
        int dk = SORT_CMP(arr + (i - 1), arr + i);
        if (dk > 0)
        {
            return eFail;
        }
        if (dk == 0 && arr[i - 1].val > arr[i].val)
        {
            return eUnstable;
        }
    }
    return eOk;
}

void PrintArray(char *s, SORT_TYPE *arr, int Len)
{
    printf("%s:", s);
    for (int i = 0; i < Len; i++)
    {
        printf(" %d:%d", arr[i].key, arr[i].val);
    }
    printf("\n");
}

extern "C" int xcmp(const void *a, const void *b)
{
    return SORT_CMP((const SORT_TYPE *)a, (const SORT_TYPE *)b);
}

void qtest(SORT_TYPE *arr, int Len)
{
    qsort(arr, Len, sizeof(SORT_TYPE), xcmp);
}

bool xlt(SORT_TYPE a, SORT_TYPE b)
{
    return SORT_CMP(&a, &b) < 0;
}

void qsttest(SORT_TYPE *arr, int Len)
{
    std::stable_sort(arr, arr + Len, xlt);
}

void Check(SORT_TYPE *arr, int *KeyCntr, int Len, int NKey, eAlgorithm alg)
{
    GenArray(arr, KeyCntr, Len, NKey);
    printf("%s N: %d, NK: %d ", alg_names[alg], Len, NKey);
    //PrintArray("Input",arr,Len);
    NCmps = 0;
    long ct = clock();
    switch (alg)
    {
        case eStableSort:
            qsttest(arr, Len);
            break;
        case eGrailSort:
        {
            SORT_TYPE buffer[512];
            GrailSortWithBuffer(arr, Len, sizeof(SORT_TYPE), buffer, sizeof(buffer)/sizeof(SORT_TYPE), xcmp);
            break;
        }
        case eQSort:
            qsort(arr, Len, sizeof(SORT_TYPE), NEW_SORT_CMP);
            break;
        default:
            break;
    }
    printf("Cmps: %I64d, time: %ld ms ", NCmps, clock() - ct);
    eTestResult result = TestArray(arr, Len);
    printf("%s\n", test_msgs[result]);
}

void CheckTwo(SORT_TYPE *A, int *Keys, int L, int NK)
{
    int h = seed;
    Check(A, Keys, L, NK, eStableSort);
    seed = h;
    Check(A, Keys, L, NK, eGrailSort);
    seed = h;
    Check(A, Keys, L, NK, eQSort);
}



int main()
{
    int NMax = 100000000;
    int NMaxKey = 200000;
    SORT_TYPE *A = new SORT_TYPE[NMax];
    int *Keys = new int[NMaxKey];

    /*
    Check(A,Keys,NMax,0,false);
    Check(A,Keys,NMax,0,true);
    */

#if 0
    for (int u = 100; u <= NMax; u *= 10)
    {
        for (int v = 2; v <= u && v <= NMaxKey; v *= 2)
        {
            CheckTwo(A, Keys, u, v - 1);
        }
    }
#else
    CheckTwo(A, Keys, 1000000, 1023);
    CheckTwo(A, Keys, 1000000, 2047);
    CheckTwo(A, Keys, 10000000, 4095);
    CheckTwo(A, Keys, 10000000, 8191);
    CheckTwo(A, Keys, 100000000, 16383);
    CheckTwo(A, Keys, 100000000, 32767);
    CheckTwo(A, Keys, 100000000, 32767);
    CheckTwo(A, Keys, 100000000, 16383);
    CheckTwo(A, Keys, 10000000, 8191);
    CheckTwo(A, Keys, 10000000, 4095);
    CheckTwo(A, Keys, 1000000, 2047);
    CheckTwo(A, Keys, 1000000, 1023);
#endif

    return 0;
}

