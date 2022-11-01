/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

// size와 할당 비트를 합해서 header와 footer의 값을 계산
#define PACK(size, alloc) ((size) | (alloc))

// p가 참조하는 워드를 읽어서 return하거나 val값을 저장
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// predecessor와 successor 포인터 초기화
#define INIT_POINTER(p, addr) *(char **)(p) = addr;

// header와 footer의 값을 보고 각각 size와 할당 비트를 return
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp : 블록 포인터
// header나 footer를 가리키는 포인터를 return
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// bp의 predecessor와 successor를 return
#define FREE_LIST_HEADER(bp) (*(void **)(bp))
#define PRED(bp) (*(void **)(bp))
#define SUCC(bp) (*(void **)(bp + WSIZE))

// 다음과 이전 블록의 블록 포인터를 각각 return
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/*
 * mm_init - initialize the malloc package.
 */

// 전체 블록 리스트 header
static char *block_list_header = NULL;

// 가용 블록 리스트 header
static char *free_list_header = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);

static void remove_free_b(void *bp);
static void append_free_b(void *bp);
static int cul_idx(size_t size);

int mm_init(void)
{
    if ((block_list_header = mem_sbrk(16 * WSIZE)) == (void *)-1)
        return -1;

    PUT(block_list_header, 0);

    PUT(block_list_header + (1 * WSIZE), PACK((14 * 4), 1));
    PUT(block_list_header + (14 * WSIZE), PACK((14 * 4), 1));

    for (int i = 2; i < 14; i++)
        INIT_POINTER(block_list_header + (WSIZE * i), NULL);

    PUT(block_list_header + (15 * WSIZE), PACK(0, 1));

    block_list_header += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    // 요구하는 size가 0면 NULL return
    if (size == 0)
        return NULL;

    // 최소 asize = 16 = 2 * DSIZE = header(4) + footer(4) + payload(8)
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    // size + (DSIZE - 1) -> size에 데이터 정렬에 맞춰 padding 부분 추가
    // + DSIZE -> header와 footer 블록
    else
        asize = DSIZE * ((size + (DSIZE - 1) + (DSIZE)) / DSIZE);

    if ((bp = first_fit(asize)) != NULL)
    {
        // 메모리를 할당하고 bp return
        place(bp, asize);
        return bp;
    }

    // asize를 수용할 수 있는 가용 블록이 없으면
    // 추가해야하는 heap 크기
    extendsize = MAX(asize, CHUNKSIZE);

    // heap 추가 요청
    // 실패하면 NULL return
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    // 성공하면 메모리를 할당하고 bp return
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer의 할당 비트를 변경
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 앞뒤 블록과 연결 -> 즉시 연결
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    // 원래 size
    size_t original_size = GET_SIZE(HDRP(bp));

    // 새로운 size 크기만큼 할당
    void *new_bp = mm_malloc(size);

    // size 변화가 없으면 원래 bp return
    if (new_bp == NULL)
        return bp;

    // 새로 할당 받은 블록에 원래 data 옮김
    memcpy(new_bp, bp, MIN(size, original_size));

    // 원래 블록 반환
    mm_free(bp);

    // 새로운 블록 주소 return
    return new_bp;
}

// heap 크기 증가 요청
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // word가 짝수가 되도록 size 조정
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // heap 추가 요청
    // 실패시 NULL return
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 추가된 메모리를 가용 블록으로 초기화
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // epilogue 위치 변경
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 이전 블록이 가용 블록이면 연결 -> 즉시 연결
    return coalesce(bp);
}

// 가용 블록 연결
static void *coalesce(void *bp)
{
    // 이전 블록과 다음 블록의 할당 비트
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));

    // 다음 블록만 가용 블록
    if (prev_alloc && !next_alloc)
    {
        remove_free_b(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 이전 블록만 가용 블록
    else if (!prev_alloc && next_alloc)
    {
        remove_free_b(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 이전 블록과 다음 블록 둘 다 가용 블록
    else if (!prev_alloc && !next_alloc)
    {
        remove_free_b(PREV_BLKP(bp));
        remove_free_b(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    append_free_b(bp);

    return bp;
}

// first fit으로 가용 블록 탐색
static void *first_fit(size_t asize)
{
    int idx = cul_idx(asize);
    void *cur_block;

    cur_block = FREE_LIST_HEADER(block_list_header + (WSIZE * idx));
    while (cur_block != NULL && GET_SIZE(HDRP(cur_block)) < asize)
        cur_block = SUCC(cur_block);

    if (cur_block == NULL)
        for (idx++; idx < 12; idx++)
        {
            cur_block = FREE_LIST_HEADER(block_list_header + (WSIZE * idx));
            if (cur_block != NULL)
                break;
        }

    // remove_free_b(cur_block);
    return cur_block;
}

// 가용 블록에서 적당한 크기의 블록 할당
static void place(void *bp, size_t asize)
{
    // 가용 블록 전체 크기
    size_t csize = GET_SIZE(HDRP(bp));

    // 전체 크기에서 필요한 크기를 빼고 남은 크기
    size_t remain = csize - asize;

    // 가용 블록을 가용 블록 리스트에서 삭제
    remove_free_b(bp);

    // 남은 크기가 최소 블록 크기보다 작으면
    if (remain < (2 * DSIZE))
    {
        // 전체 크기를 모두 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

    // 남은 크기가 최소 블록 크기보다 크거나 같으면
    else
    {
        // 필요한 크기만큼 할당하고
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 남은 크기를 가용블록으로 만듬
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));

        coalesce(bp);
    }
}

// 가용 블록 리스트에서 특정 블록을 삭제
static void remove_free_b(void *bp)
{
    int idx = cul_idx(GET_SIZE(HDRP(bp)));
    void *header = FREE_LIST_HEADER(block_list_header + (WSIZE * idx));

    if (bp == NULL)
        return;

    if (header == bp)
    {
        FREE_LIST_HEADER(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);
    }
    else
    {
        if (SUCC(bp) != NULL)
            PRED(SUCC(bp)) = PRED(bp);
        SUCC(PRED(bp)) = SUCC(bp);
    }
}

// 가용 블록 리스트 앞에 새로운 블록을 추가
static void append_free_b(void *bp)
{
    int idx = cul_idx(GET_SIZE(HDRP(bp)));
    void *cur_block = FREE_LIST_HEADER(block_list_header + (WSIZE * idx));

    while (SUCC(cur_block) == NULL && GET_SIZE(HDRP(SUCC(cur_block))) > GET_SIZE(HDRP(bp)))
        cur_block = SUCC(cur_block);

    PRED(bp) = cur_block;
    SUCC(bp) = SUCC(cur_block);

    SUCC(PRED(bp)) = bp;
    if (SUCC(bp) != NULL)
        PRED(SUCC(bp)) = bp;
}

static int cul_idx(size_t size)
{
    int idx = -4;

    for (size--; size > 0; size /= 2)
        idx++;

    return idx;
}