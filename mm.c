#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

// #define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_printblock(a) printblock(a)
#else
#define dbg_printf(...)
#define dbg_printblock(a)
#endif

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define PUT_ADDR(p, val) (*(long *)(p) = (long)(val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXTP(bp) (long *)((char *)(bp))
#define PREVP(bp) (long *)((char *)(bp) + DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define ALIGNMENT 8

#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p) ((size_t *)(((char *)(p)) - SIZE_T_SIZE))

#define MIN_BLKSIZE 24

#define NUM_FREELIST 15

static char *heap_listp;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

static void delete_freenode(void *bp);
static void insert_freenode(void *bp);
static void *getroot(int class);
static int getclass(size_t size);
static int getrangeforclass(int class);

static void printblock(void *bp);
static void checkblock(void *bp);
static void printfreelist();

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(DSIZE + NUM_FREELIST * DSIZE * 2)) == NULL)
        return -1;
    // pedding block
    PUT(heap_listp, 0);

    // epilogue block
    PUT(heap_listp + 2 * NUM_FREELIST * DSIZE + WSIZE, PACK(0, 1));

    // 첫번째 prologue block의 bp로 조정
    heap_listp += DSIZE;

    // prologue block 초기화
    for (int i = 0; i < NUM_FREELIST; i++)
    {
        char *root = getroot(i);
        PUT(root - WSIZE, PACK(2 * DSIZE, 1));
        PUT_ADDR(root, NULL);
        PUT(root + DSIZE, PACK(2 * DSIZE, 1));
    }

    // heap 추가
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    dbg_printf("Calling mm_malloc........");
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    asize = MAX(ALIGN(size + SIZE_T_SIZE), MIN_BLKSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        dbg_printf("place succeed: ");
        dbg_printblock(bp);
        dbg_printblock(NEXT_BLKP(bp));
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    dbg_printf("Calling mm_free........");
    if (!bp)
        return;
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *oldptr, size_t size)
{
    dbg_printf("Calling mm_relloc........");
    void *newptr;

    // size가 0이면 free와 동일
    if (size == 0)
    {
        mm_free(oldptr);
        return 0;
    }

    // 변경할 할당 블록을 입력 안하면 malloc과 동일
    if (oldptr == NULL)
        return mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if ((newptr = mm_malloc(size)) == NULL)
    {
        return 0;
    }

    memcpy(newptr, oldptr, MIN(size, GET_SIZE(HDRP(oldptr))));

    mm_free(oldptr);

    return newptr;
}

// heap 공간 추가
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

// 찾은 가용 블록에 할당
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    delete_freenode(bp);

    if ((csize - asize) >= MIN_BLKSIZE)
    {
        dbg_printf("SPLITTING: ");
        dbg_printblock(bp);
        dbg_printf("SPLITTED: ");
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        dbg_printblock(bp);
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        dbg_printblock(bp);
        insert_freenode(bp);

        dbg_printblock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// 가용리스트 탐색 - first fit
static void *find_fit(size_t asize)
{
    dbg_printf("FINDING FIT: ");
    void *bp;
    int class = getclass(asize);

    // 현재 size class와 그것보다 큰 size class에서 탐색
    for (int i = class; i < NUM_FREELIST; i++)
    {
        void *root = getroot(i);

        // 가용 리스트 앞에서부터 탐색
        for (bp = root; bp != NULL; bp = (char *)*NEXTP(bp))
        {
            dbg_printf(" %lx > ", (long)bp);
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            {
                dbg_printf("FOUND!\n");
                return bp;
            }
        }
    }

    dbg_printf("NOT FOUND :(\n");
    return NULL;
}

// 연결
static void *coalesce(void *bp)
{
    dbg_printf("Coalescing\n");
    dbg_printblock(bp);
    dbg_printblock(PREV_BLKP(bp));
    dbg_printblock(NEXT_BLKP(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 앞뒤 블록 모두 할당 블록
    if (prev_alloc && next_alloc)
    {
        insert_freenode(bp);
        return bp;
    }

    // 다음 블록만 가용 브록
    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_freenode(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_freenode(bp);
        dbg_printblock(bp);
        return (bp);
    }

    // 이전 블록만 가용 브록
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_freenode(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        insert_freenode(PREV_BLKP(bp));
        dbg_printblock(PREV_BLKP(bp));
        return (PREV_BLKP(bp));
    }

    // 앞뒤 블록 모두 가용 블록
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_freenode(PREV_BLKP(bp));
        delete_freenode(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        insert_freenode(PREV_BLKP(bp));
        dbg_printblock(PREV_BLKP(bp));
        return (PREV_BLKP(bp));
    }
}

// 가용 블록 삭제
static void delete_freenode(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    void *root = getroot(getclass(size));

    void *next_free_block = (void *)*NEXTP(bp);
    void *prev_free_block = (void *)*PREVP(bp);

    if (next_free_block != NULL)
    {
        if (prev_free_block != NULL)
        { // 중간에서 삭제
            PUT_ADDR(NEXTP(prev_free_block), next_free_block);
            PUT_ADDR(PREVP(next_free_block), prev_free_block);
        }
        else
        { // 리스트 처음에서 삭제
            PUT_ADDR(NEXTP(root), next_free_block);
            PUT_ADDR(PREVP(next_free_block), NULL);
        }
    }
    else
    {
        if (prev_free_block != NULL)
        { // 리스트 마지막에서 삭제
            PUT_ADDR(NEXTP(prev_free_block), NULL);
        }
        else
        { // 마지막 블록 삭제
            PUT_ADDR(NEXTP(root), NULL);
        }
    }
}

// 가용 리스트 맨 앞에 가용 블록 추가
static void insert_freenode(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    void *root = getroot(getclass(size));

    void *cur_free_block = (void *)*NEXTP(root);
    void *prev_free_block = NULL;

    while (cur_free_block != NULL && size > GET_SIZE(HDRP(cur_free_block)))
    {
        prev_free_block = cur_free_block;
        cur_free_block = (void *)*NEXTP(cur_free_block);
    }

    if (cur_free_block != NULL)
    {
        if (prev_free_block != NULL)
        { // 리스트 중간에 삽입
            PUT_ADDR(NEXTP(bp), cur_free_block);
            PUT_ADDR(PREVP(bp), prev_free_block);

            PUT_ADDR(NEXTP(prev_free_block), bp);
            PUT_ADDR(PREVP(cur_free_block), bp);
        }
        else
        { // 리스트 처음에 삽입
            PUT_ADDR(NEXTP(bp), cur_free_block);
            PUT_ADDR(PREVP(bp), NULL);

            PUT_ADDR(PREVP(cur_free_block), bp);
            PUT_ADDR(NEXTP(root), bp);
        }
    }
    else
    {
        if (prev_free_block != NULL)
        { // 리스트 마지막에 삽입
            PUT_ADDR(NEXTP(bp), NULL);
            PUT_ADDR(PREVP(bp), prev_free_block);

            PUT_ADDR(NEXTP(prev_free_block), bp);
        }
        else
        { // 빈 리스트에 삽입
            PUT_ADDR(NEXTP(bp), NULL);
            PUT_ADDR(PREVP(bp), NULL);

            PUT_ADDR(NEXTP(root), bp);
        }
    }
}

// 각 prologue block bp 구함
static void *getroot(int class)
{
    return heap_listp + class * 2 * DSIZE;
}

static int getrangeforclass(int class)
{
    return 1 << (class + 2);
}

// size에 맞는 size class 찾기
static int getclass(size_t size)
{
    int block = size / DSIZE;
    for (int i = 0; i < NUM_FREELIST - 1; i++)
    {
        if (block <= getrangeforclass(i) && block > getrangeforclass(i - 1))
        {
            return i;
        }
    }
    return NUM_FREELIST - 1;
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;
    long next, prev;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }

    if (!halloc || (char *)bp < (heap_listp + 2 * NUM_FREELIST * DSIZE))
    {
        next = *NEXTP(bp);
        prev = *PREVP(bp);
        printf("%p: header: [%d:%c] next: %lx prev: %lx footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'), next, prev,
               (int)fsize, (falloc ? 'a' : 'f'));
    }
    else
    {
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
               (int)hsize, (halloc ? 'a' : 'f'),
               (int)fsize, (falloc ? 'a' : 'f'));
    }
}

static void printfreelist()
{

    for (int i = 0; i < NUM_FREELIST; i++)
    {
        printf("Free list %d: ", i);
        char *bp = getroot(i);
        for (; bp != NULL; bp = (char *)*NEXTP(bp))
        {
            printf(" %lx -> ", (long)bp);
        }
        printf("END\n");
    }
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}