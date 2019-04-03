/********* Grail sorting *********************************/
/*                                                       */
/* (c) 2013 by Andrey Astrelin                           */
/*                                                       */
/*                                                       */
/* Stable sorting that works in O(N*log(N)) worst time   */
/* and uses O(1) extra memory                            */
/*                                                       */
/* Define SORT_TYPE and SORT_CMP                         */
/* and then call GrailSort() function                    */
/*                                                       */
/* For sorting with fixed external buffer (512 items)    */
/* use GrailSortWithBuffer()                             */
/*                                                       */
/* For sorting with dynamic external buffer (O(sqrt(N)) items) */
/* use GrailSortWithDynBuffer()                          */
/*                                                       */
/* Also classic in-place merge sort is implemented       */
/* under the name of RecStableSort()                     */
/*                                                       */
/*********************************************************/

#include<memory.h>
#include<malloc.h>
#define GRAIL_EXT_BUFFER_LENGTH 512

typedef int (*compare_fn)(const void *, const void*);

/* Byte-wise swap two items of size SIZE. */
#define SWAP(a, b, size)                \
    do                                  \
    {                                   \
        size_t __size = (size);         \
        char *__a = (char *)(a);        \
        char *__b = (char *)(b);        \
        do                              \
        {                               \
            char __tmp = *__a;          \
            *__a++ = *__b;              \
            *__b++ = __tmp;             \
        } while (--__size > 0);         \
    } while (0)

inline void grail_swap1(char *a, char *b, size_t size)
{
    SWAP(a, b, size);
}

inline void grail_swapN(char *a, char *b, size_t size, int n)
{
    while (n--)
    {
        grail_swap1(a, b, size);
        a += size;
        b += size;
    }
}

static void grail_rotate(char *a, size_t size, int L1, int L2)
{
    while (L1 && L2)
    {
        if (L1 <= L2)
        {
            grail_swapN(a, &a[size * L1], size, L1);
            a = &a[size * L1];
            L2 -= L1;
        }
        else
        {
            grail_swapN(&a[size * (L1 - L2)], &a[size * L1], size, L2);
            L1 -= L2;
        }
    }
}

static int grail_BinSearchLeft(char *arr, size_t len, size_t size, char *key, compare_fn compare)
{
    int a = -1, b = len, c;
    while (a < b - 1)
    {
        c = a + ((b - a) >> 1);
        if (compare(&arr[size * c], key) >= 0)
        {
            b = c;
        }
        else
        {
            a = c;
        }
    }
    return b;
}

static int grail_BinSearchRight(char *arr, size_t len, size_t size, char *key, compare_fn compare)
{
    int a = -1, b = len, c;
    while (a < b - 1)
    {
        c = a + ((b - a) >> 1);
        if (compare(&arr[size * c], key) > 0)
        {
            b = c;
        }
        else
        {
            a = c;
        }
    }
    return b;
}

// cost: 2*len+nk^2/2
static int grail_FindKeys(char *arr, size_t len, size_t size, int nkeys, compare_fn compare)
{
    int h = 1, h0 = 0; // first key is always here
    int u = 1, r;
    while (u < len && h < nkeys)
    {
        r = grail_BinSearchLeft(&arr[size * h0], h, size, &arr[size * u], compare);
        if (r == h || compare(&arr[size * u], &arr[size * (h0 + r)]) != 0)
        {
            grail_rotate(&arr[size * h0], size, h, u - (h0 + h));
            h0 = u - h;
            grail_rotate(&arr[size * (h0 + r)], size, h - r, 1);
            h++;
        }
        u++;
    }
    grail_rotate(arr, size, h0, h);
    return h;
}

// cost: min(L1,L2)^2+max(L1,L2)
static void grail_MergeWithoutBuffer(char *arr, size_t size, size_t len1, size_t len2, compare_fn compare)
{
    int h;
    if (len1 < len2)
    {
        while (len1)
        {
            h = grail_BinSearchLeft(&arr[size * len1], len2, size, arr, compare);
            if (h != 0)
            {
                grail_rotate(arr, size, len1, h);
                arr += size * h;
                len2 -= h;
            }
            if (len2 == 0)
            {
                break;
            }
            do
            {
                arr += size;
                len1--;
            }
            while (len1 && compare(arr, &arr[size * len1]) <= 0);
        }
    }
    else
    {
        while (len2)
        {
            h = grail_BinSearchRight(arr, len1, size, &arr[size * (len1 + len2 - 1)], compare);
            if (h != len1)
            {
                grail_rotate(&arr[size * h], size, len1 - h, len2);
                len1 = h;
            }
            if (len1 == 0)
            {
                break;
            }
            do
            {
                len2--;
            }
            while (len2 && compare(&arr[size * (len1 - 1)], &arr[size * (len1 + len2 - 1)]) <= 0);
        }
    }
}

// arr[M..-1] - buffer, arr[0,L1-1]++arr[L1,L1+L2-1] -> arr[M,M+L1+L2-1]
static void grail_MergeLeft(char *arr, size_t size, int L1, int L2, int M, compare_fn compare)
{
    int p0 = 0, p1 = L1;
    L2 += L1;
    while (p1 < L2)
    {
        if (p0 == L1 || compare(&arr[size * p0], &arr[size * p1]) > 0)
        {
            grail_swap1(&arr[size * (M++)], &arr[size * (p1++)], size);
        }
        else
        {
            grail_swap1(&arr[size * (M++)], &arr[size * (p0++)], size);
        }
    }
    if (M != p0)
    {
        grail_swapN(&arr[size * M], &arr[size * p0], size, L1 - p0);
    }
}

static void grail_MergeRight(char *arr, size_t size, int L1, int L2, int M, compare_fn compare)
{
    int p0 = L1 + L2 + M - 1;
    int p1 = L1 - 1;
    int p2 = L1 + L2 - 1;

    while (p1 >= 0)
    {
        if (p2 < L1 || compare(&arr[size * p1], &arr[size * p2]) > 0)
        {
            grail_swap1(&arr[size * (p0--)], &arr[size * (p1--)], size);
        }
        else
        {
            grail_swap1(&arr[size * (p0--)], &arr[size * (p2--)], size);
        }
    }
    if (p2 != p0)
    {
        while (p2 >= L1)
        {
            grail_swap1(&arr[size * (p0--)], &arr[size * (p2--)], size);
        }
    }
}

static void grail_SmartMergeWithBuffer(char *arr, size_t size, int *alen1, int *atype, int len2, int lkeys, compare_fn compare)
{
    int p0 = -lkeys, p1 = 0, p2 = *alen1, q1 = p2, q2 = p2 + len2;
    int ftype = 1 - *atype; // 1 if inverted
    while (p1 < q1 && p2 < q2)
    {
        if (compare(&arr[size * p1], &arr[size * p2]) - ftype < 0)
        {
            grail_swap1(&arr[size * (p0++)], &arr[size * (p1++)], size);
        }
        else
        {
            grail_swap1(&arr[size * (p0++)], &arr[size * (p2++)], size);
        }
    }
    if (p1 < q1)
    {
        *alen1 = q1 - p1;
        while (p1 < q1)
        {
            grail_swap1(&arr[size * (--q1)], &arr[size * (--q2)], size);
        }
    }
    else
    {
        *alen1 = q2 - p2;
        *atype = ftype;
    }
}

static void grail_SmartMergeWithoutBuffer(char *arr, size_t size, int *alen1, int *atype, int _len2, compare_fn compare)
{
    int len1, len2, ftype, h;

    if (!_len2)
    {
        return;
    }
    len1 = *alen1;
    len2 = _len2;
    ftype = 1 - *atype;
    if (len1 && compare(&arr[size * (len1 - 1)], &arr[size * len1]) - ftype >= 0)
    {
        while (len1)
        {
            h = ftype ? grail_BinSearchLeft(&arr[size * len1], len2, size, arr, compare) : grail_BinSearchRight(&arr[size *len1], len2, size, arr, compare);
            if (h != 0)
            {
                grail_rotate(arr, size, len1, h);
                arr += size * h;
                len2 -= h;
            }
            if (len2 == 0)
            {
                *alen1 = len1;
                return;
            }
            do
            {
                arr += size;
                len1--;
            }
            while (len1 && compare(arr, &arr[size * len1]) - ftype < 0);
        }
    }
    *alen1 = len2;
    *atype = ftype;
}

/***** Sort With Extra Buffer *****/

// arr[M..-1] - free, arr[0,L1-1]++arr[L1,L1+L2-1] -> arr[M,M+L1+L2-1]
static void grail_MergeLeftWithXBuf(char *arr, size_t size, int L1, int L2, int M, compare_fn compare)
{
    int p0 = 0;
    int p1 = L1;

    L2 += L1;
    while (p1 < L2)
    {
        if (p0 == L1 || compare(&arr[size * p0], &arr[size * p1]) > 0)
        {
            memcpy(&arr[size * (M++)], &arr[size * (p1++)], size);
        }
        else
        {
            memcpy(&arr[size * (M++)], &arr[size * (p0++)], size);
        }
    }
    if (M != p0)
    {
        while (p0 < L1)
        {
            memcpy(&arr[size * (M++)], &arr[size * (p0++)], size);
        }
    }
}

static void grail_SmartMergeWithXBuf(char *arr, size_t size, int *alen1, int *atype, int len2, int lkeys, compare_fn compare)
{
    int p0 = -lkeys, p1 = 0, p2 = *alen1, q1 = p2, q2 = p2 + len2;
    int ftype = 1 - *atype; // 1 if inverted
    while (p1 < q1 && p2 < q2)
    {
        if (compare(&arr[size * p1], &arr[size * p2]) - ftype < 0)
        {
            memcpy(&arr[size * (p0++)], &arr[size * (p1++)], size);
        }
        else
        {
            memcpy(&arr[size * (p0++)], &arr[size * (p2++)], size);
        }
    }
    if (p1 < q1)
    {
        *alen1 = q1 - p1;
        while (p1 < q1)
        {
            memcpy(&arr[size * (--q2)], &arr[size * (--q1)], size);
        }
    }
    else
    {
        *alen1 = q2 - p2;
        *atype = ftype;
    }
}

// arr - starting array. arr[-lblock..-1] - buffer (if havebuf).
// lblock - length of regular blocks. First nblocks are stable sorted by 1st elements and key-coded
// keys - arrays of keys, in same order as blocks. key<midkey means stream A
// nblock2 are regular blocks from stream A. llast is length of last (irregular) block from stream B, that should go before nblock2 blocks.
// llast=0 requires nblock2=0 (no irregular blocks). llast>0, nblock2=0 is possible.
static void grail_MergeBuffersLeftWithXBuf(char *keys, char *midkey, char *arr, size_t size, int nblock, int lblock, int nblock2, int llast, compare_fn compare)
{
    int l, prest, lrest, frest, pidx, cidx, fnext, plast;

    if (nblock == 0)
    {
        l = nblock2 * lblock;
        grail_MergeLeftWithXBuf(arr, l, size, llast, -lblock, compare);
        return;
    }

    lrest = lblock;
    frest = compare(keys, midkey) < 0 ? 0 : 1;
    pidx = lblock;
    for (cidx = 1; cidx < nblock; cidx++, pidx += lblock)
    {
        prest = pidx - lrest;
        fnext = compare(&keys[size * cidx], midkey) < 0 ? 0 : 1;
        if (fnext == frest)
        {
            memcpy(&arr[size * (prest - lblock)], &arr[size * prest], lrest * size);
            prest = pidx;
            lrest = lblock;
        }
        else
        {
            grail_SmartMergeWithXBuf(&arr[size * prest], size, &lrest, &frest, lblock, lblock, compare);
        }
    }
    prest = pidx - lrest;
    if (llast)
    {
        plast = pidx + lblock * nblock2;
        if (frest)
        {
            memcpy(&arr[size * (prest - lblock)], &arr[size * prest], lrest * size);
            prest = pidx;
            lrest = lblock * nblock2;
            frest = 0;
        }
        else
        {
            lrest += lblock * nblock2;
        }
        grail_MergeLeftWithXBuf(&arr[size * prest], size, lrest, llast, -lblock, compare);
    }
    else
    {
        memcpy(&arr[size * (prest - lblock)], &arr[size * prest], lrest * size);
    }
}

/***** End Sort With Extra Buffer *****/

// build blocks of length K
// input: [-K,-1] elements are buffer
// output: first K elements are buffer, blocks 2*K and last subblock sorted
static void grail_BuildBlocks(char *arr, int L, size_t size, int K, char *extbuf, size_t LExtBuf, compare_fn compare)
{
    int m, u, h, p0, p1, rest, restk, p, kbuf;
    kbuf = K < LExtBuf ? K : LExtBuf;
    while (kbuf & (kbuf - 1))
    {
        kbuf &= kbuf - 1;    // max power or 2 - just in case
    }

    if (kbuf)
    {
        memcpy(extbuf, arr - (size * kbuf), kbuf * size);
        for (m = 1; m < L; m += 2)
        {
            u = 0;
            if (compare(&arr[size * (m - 1)], &arr[size * m]) > 0)
            {
                u = 1;
            }
            memcpy(&arr[size * (m - 3)], &arr[size * (m - 1 + u)], size);
            memcpy(&arr[size * (m - 2)], &arr[size * (m - u)], size);
        }
        if (L % 2)
        {
            memcpy(&arr[size * (L - 3)], &arr[size * (L - 1)], size);
        }
        arr -= size * 2;
        for (h = 2; h < kbuf; h *= 2)
        {
            p0 = 0;
            p1 = L - 2 * h;
            while (p0 <= p1)
            {
                grail_MergeLeftWithXBuf(&arr[size * p0], size, h, h, -h, compare);
                p0 += 2 * h;
            }
            rest = L - p0;
            if (rest > h)
            {
                grail_MergeLeftWithXBuf(&arr[size * p0], size, h, rest - h, -h, compare);
            }
            else
            {
                for (; p0 < L; p0++)
                {
                    memcpy(&arr[size * (p0 - h)], &arr[size * p0], size);
                }
            }
            arr -= size * h;
        }
        memcpy(&arr[size * L], extbuf, kbuf * size);
    }
    else
    {
        for (m = 1; m < L; m += 2)
        {
            u = 0;
            if (compare(&arr[size * (m - 1)], &arr[size * m]) > 0)
            {
                u = 1;
            }
            grail_swap1(&arr[size * (m - 3)], &arr[size * (m - 1 + u)], size);
            grail_swap1(&arr[size * (m - 2)], &arr[size * (m - u)], size);
        }
        if (L % 2)
        {
            grail_swap1(&arr[size * (L - 1)], &arr[size * (L - 3)], size);
        }
        arr -= size * 2;
        h = 2;
    }
    for (; h < K; h *= 2)
    {
        p0 = 0;
        p1 = L - 2 * h;
        while (p0 <= p1)
        {
            grail_MergeLeft(&arr[size * p0], size, h, h, -h, compare);
            p0 += 2 * h;
        }
        rest = L - p0;
        if (rest > h)
        {
            grail_MergeLeft(&arr[size * p0], size, h, rest - h, -h, compare);
        }
        else
        {
            grail_rotate(&arr[size * (p0 - h)], size, h, rest);
        }
        arr -= size * h;
    }
    restk = L % (2 * K);
    p = L - restk;
    if (restk <= K)
    {
        grail_rotate(&arr[size * p], size, restk, K);
    }
    else
    {
        grail_MergeRight(&arr[size * p], size, K, restk - K, K, compare);
    }
    while (p > 0)
    {
        p -= 2 * K;
        grail_MergeRight(&arr[size * p], size, K, K, K, compare);
    }
}

// arr - starting array. arr[-lblock..-1] - buffer (if havebuf).
// lblock - length of regular blocks. First nblocks are stable sorted by 1st elements and key-coded
// keys - arrays of keys, in same order as blocks. key<midkey means stream A
// nblock2 are regular blocks from stream A. llast is length of last (irregular) block from stream B, that should go before nblock2 blocks.
// llast=0 requires nblock2=0 (no irregular blocks). llast>0, nblock2=0 is possible.
static void grail_MergeBuffersLeft(char *keys, char *midkey, char *arr, size_t size, int nblock, int lblock, bool havebuf, int nblock2, int llast, compare_fn compare)
{
    int l, prest, lrest, frest, pidx, cidx, fnext, plast;

    if (nblock == 0)
    {
        l = nblock2 * lblock;
        if (havebuf)
        {
            grail_MergeLeft(arr, size, l, llast, -lblock, compare);
        }
        else
        {
            grail_MergeWithoutBuffer(arr, size, l, llast, compare);
        }
        return;
    }

    lrest = lblock;
    frest = compare(keys, midkey) < 0 ? 0 : 1;
    pidx = lblock;
    for (cidx = 1; cidx < nblock; cidx++, pidx += lblock)
    {
        prest = pidx - lrest;
        fnext = compare(&keys[size * cidx], midkey) < 0 ? 0 : 1;
        if (fnext == frest)
        {
            if (havebuf)
            {
                grail_swapN(&arr[size * (prest - lblock)], &arr[size * prest], size, lrest);
            }
            prest = pidx;
            lrest = lblock;
        }
        else
        {
            if (havebuf)
            {
                grail_SmartMergeWithBuffer(&arr[size * prest], size, &lrest, &frest, lblock, lblock, compare);
            }
            else
            {
                grail_SmartMergeWithoutBuffer(&arr[size * prest], size, &lrest, &frest, lblock, compare);
            }

        }
    }
    prest = pidx - lrest;
    if (llast)
    {
        plast = pidx + lblock * nblock2;
        if (frest)
        {
            if (havebuf)
            {
                grail_swapN(&arr[size * (prest - lblock)], &arr[size * prest], size, lrest);
            }
            prest = pidx;
            lrest = lblock * nblock2;
            frest = 0;
        }
        else
        {
            lrest += lblock * nblock2;
        }
        if (havebuf)
        {
            grail_MergeLeft(&arr[size * prest], size, lrest, llast, -lblock, compare);
        }
        else
        {
            grail_MergeWithoutBuffer(&arr[size * prest], size, lrest, llast, compare);
        }
    }
    else
    {
        if (havebuf)
        {
            grail_swapN(&arr[size * prest], &arr[size * (prest - lblock)], size, lrest);
        }
    }
}

static void grail_SortIns(char *arr, size_t len, size_t size, compare_fn compare)
{
    int i, j;
    for (i = 1; i < len; i++)
    {
        for (j = i - 1; j >= 0 && compare(&arr[size * (j + 1)], &arr[size * j]) < 0; j--)
        {
            grail_swap1(&arr[size * j], &arr[size * (j + 1)], size);
        }
    }
}

static void grail_LazyStableSort(char *arr, size_t L, size_t size, compare_fn compare)
{
    int m, u, h, p0, p1, rest;
    for (m = 1; m < L; m += 2)
    {
        u = 0;
        if (compare(&arr[size * (m - 1)], &arr[size * m]) > 0)
        {
            grail_swap1(&arr[size * (m - 1)], &arr[size * m], size);
        }
    }
    for (h = 2; h < L; h *= 2)
    {
        p0 = 0;
        p1 = L - 2 * h;
        while (p0 <= p1)
        {
            grail_MergeWithoutBuffer(&arr[size * p0], size, h, h, compare);
            p0 += 2 * h;
        }
        rest = L - p0;
        if (rest > h)
        {
            grail_MergeWithoutBuffer(&arr[size * p0], size, h, rest - h, compare);
        }
    }
}

// keys are on the left of arr. Blocks of length LL combined. We'll combine them in pairs
// LL and nkeys are powers of 2. (2*LL/lblock) keys are guarantied
static void grail_CombineBlocks(char *keys, char *arr, size_t len, size_t size, int LL, int lblock, bool havebuf, char *xbuf, compare_fn compare)
{
    int M, nkeys, b, NBlk, midkey, lrest, u, p, v, kc, nbl2, llast;
    char *arr1;

    M = len / (2 * LL);
    lrest = len % (2 * LL);
    nkeys = (2 * LL) / lblock;
    if (lrest <= LL)
    {
        len -= lrest;
        lrest = 0;
    }
    if (xbuf)
    {
        memcpy(xbuf, arr - (size * lblock), lblock * size);
    }
    for (b = 0; b <= M; b++)
    {
        if (b == M && lrest == 0)
        {
            break;
        }
        arr1 = &arr[size * (b * 2 * LL)];
        NBlk = (b == M ? lrest : 2 * LL) / lblock;
        grail_SortIns(keys, NBlk + (b == M ? 1 : 0), size, compare);
        midkey = LL / lblock;
        for (u = 1; u < NBlk; u++)
        {
            p = u - 1;
            for (v = u; v < NBlk; v++)
            {
                kc = compare(&arr1[size * (p * lblock)], &arr1[size * (v * lblock)]);
                if (kc > 0 || (kc == 0 && compare(&keys[size * p], &keys[size * v]) > 0))
                {
                    p = v;
                }
            }
            if (p != u - 1)
            {
                grail_swapN(&arr1[size * ((u - 1) * lblock)], &arr1[size * (p * lblock)], size, lblock);
                grail_swap1(&keys[size * (u - 1)], &keys[size * p], size);
                if (midkey == u - 1 || midkey == p)
                {
                    midkey ^= (u - 1) ^ p;
                }
            }
        }
        nbl2 = llast = 0;
        if (b == M)
        {
            llast = lrest % lblock;
        }
        if (llast != 0)
        {
            while (nbl2 < NBlk && compare(&arr1[size * (NBlk * lblock)], &arr1[size * ((NBlk - nbl2 - 1) * lblock)]) < 0)
            {
                nbl2++;
            }
        }
        if (xbuf)
        {
            grail_MergeBuffersLeftWithXBuf(keys, &keys[size * midkey], arr1, size, NBlk - nbl2, lblock, nbl2, llast, compare);
        }
        else
        {
            grail_MergeBuffersLeft(keys, &keys[size * midkey], arr1, size, NBlk - nbl2, lblock, havebuf, nbl2, llast, compare);
        }
    }
    if (xbuf)
    {
        for (p = len; --p >= 0;)
        {
            memcpy(&arr[size * p], &arr[size * (p - lblock)], size);
        }
        memcpy(arr - (size * lblock), xbuf, lblock * size);
    }
    else if (havebuf)
    {
        do
        {
            --len;
            grail_swap1(&arr[size * len], &arr[size * (len - lblock)], size);
        }
        while(len > 0);
    }
}

void grail_commonSort(char *arr, size_t Len, size_t size, char *extbuf, size_t LExtBuf, compare_fn compare)
{
    int lblock, nkeys, findkeys, ptr, cbuf, lb, nk;
    bool havebuf, chavebuf;
    long long s;

    if (   (arr == NULL)
        || (Len < 2)
        || (size == 0))
    {
        return;
    }

    if (Len < 16)
    {
        grail_SortIns(arr, Len, size, compare);
        return;
    }

    lblock = 1;
    while (lblock * lblock < Len)
    {
        lblock *= 2;
    }
    nkeys = (Len - 1) / lblock + 1;
    findkeys = grail_FindKeys(arr, Len, size, nkeys + lblock, compare);
    havebuf = true;
    if (findkeys < nkeys + lblock)
    {
        if (findkeys < 4)
        {
            grail_LazyStableSort(arr, Len, size, compare);
            return;
        }
        nkeys = lblock;
        while (nkeys > findkeys)
        {
            nkeys /= 2;
        }
        havebuf = false;
        lblock = 0;
    }
    ptr = lblock + nkeys;
    cbuf = havebuf ? lblock : nkeys;
    if (havebuf)
    {
        grail_BuildBlocks(&arr[size * ptr], Len - ptr, size, cbuf, extbuf, LExtBuf, compare);
    }
    else
    {
        grail_BuildBlocks(&arr[size * ptr], Len - ptr, size, cbuf, NULL, 0, compare);
    }

    // 2*cbuf are built
    while (Len - ptr > (cbuf *= 2))
    {
        lb = lblock;
        chavebuf = havebuf;
        if (!havebuf)
        {
            if (nkeys > 4 && nkeys / 8 * nkeys >= cbuf)
            {
                lb = nkeys / 2;
                chavebuf = true;
            }
            else
            {
                nk = 1;
                s = (long long)cbuf * findkeys / 2;
                while (nk < nkeys && s != 0)
                {
                    nk *= 2;
                    s /= 8;
                }
                lb = (2 * cbuf) / nk;
            }
        }
        else
        {
#if 0
            if (LExtBuf != 0)
            {
                while (lb > LExtBuf && lb * lb > 2 * cbuf)
                {
                    lb /= 2;    // set size of block close to sqrt(new_block_length)
                }
            }
#endif
        }
        grail_CombineBlocks(arr, &arr[size * ptr], Len - ptr, size, cbuf, lb, chavebuf, chavebuf && lb <= LExtBuf ? extbuf : NULL, compare);
    }
    grail_SortIns(arr, ptr, size, compare);
    grail_MergeWithoutBuffer(arr, size, ptr, Len - ptr, compare);
}

void GrailSort(void *arr, size_t Len, size_t size, compare_fn compare)
{
    grail_commonSort((char *)arr, Len, size, NULL, 0, compare);
}

void GrailSortWithBuffer(void *arr, size_t Len, size_t size, void *ExtBuf, size_t LExtBuf, compare_fn compare)
{
	grail_commonSort((char *)arr, Len, size, (char *)ExtBuf, LExtBuf, compare);
}

void GrailSortWithDynBuffer(void *arr, int Len, size_t size, compare_fn compare)
{
    int L = 1;
    char *ExtBuf;
    size_t ExtBufSize;

    while (L * L < Len)
    {
        L *= 2;
    }
    ExtBufSize = L * size;
    ExtBuf = (char *)malloc(ExtBufSize);
    if (ExtBuf == NULL)
    {
        GrailSort(arr, Len, size, compare);
    }
    else
    {
        grail_commonSort((char *)arr, Len, size, ExtBuf, ExtBufSize, compare);
        free(ExtBuf);
    }
}



/****** classic MergeInPlace *************/

static void grail_RecMerge(char *A, size_t size, int L1, int L2, compare_fn compare)
{
    int K, k1, k2, m1, m2;
    if (L1 < 3 || L2 < 3)
    {
        grail_MergeWithoutBuffer(A, size, L1, L2, compare);
        return;
    }
    if (L1 < L2)
    {
        K = L1 + L2 / 2;
    }
    else
    {
        K = L1 / 2;
    }
    k1 = k2 = grail_BinSearchLeft(A, L1, size, &A[size * K], compare);
    if (k2 < L1 && compare(&A[size * k2], &A[size * K]) == 0)
    {
        k2 = grail_BinSearchRight(&A[size * k1], L1 - k1, size, &A[size * K], compare) + k1;
    }
    m1 = grail_BinSearchLeft(&A[size * L1], L2, size,&A[size * K], compare);
    m2 = m1;
    if (m2 < L2 && compare(&A[size * (L1 + m2)], &A[size * K]) == 0)
    {
        m2 = grail_BinSearchRight(&A[size * (L1 + m1)], L2 - m1, size, &A[size * K], compare) + m1;
    }
    if (k1 == k2)
    {
        grail_rotate(&A[size * k2], size, L1 - k2, m2);
    }
    else
    {
        grail_rotate(&A[size * k1], size, L1 - k1, m1);
        if (m2 != m1)
        {
            grail_rotate(&A[size * (k2 + m1)], size, L1 - k2, m2 - m1);
        }
    }
    grail_RecMerge(&A[size * (k2 + m2)], size, L1 - k2, L2 - m2, compare);
    grail_RecMerge(A, size, k1, m1, compare);
}

void RecStableSort(char *arr, int L, size_t size, compare_fn compare)
{
    int u, m, h, p0, p1, rest;

    for (m = 1; m < L; m += 2)
    {
        u = 0;
        if (compare(&arr[size * (m - 1)], &arr[size * m]) > 0)
        {
            grail_swap1(&arr[size * (m - 1)], &arr[size * m], size);
        }
    }
    for (h = 2; h < L; h *= 2)
    {
        p0 = 0;
        p1 = L - 2 * h;
        while (p0 <= p1)
        {
            grail_RecMerge(&arr[size * p0], size, h, h, compare);
            p0 += 2 * h;
        }
        rest = L - p0;
        if (rest > h)
        {
            grail_RecMerge(&arr[size * p0], size, h, rest - h, compare);
        }
    }
}
