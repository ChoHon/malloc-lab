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
#define CHUNKSIZE (1 << 15)
#define FREE_LIST_LENGTH 13
#define PAGE_SIZE (CHUNKSIZE + DSIZE) * FREE_LIST_LENGTH

#define INIT_POINTER(p, val) *(char **)(p) = val;

#define SUCC(bp) (*(void **)(bp))

static char *first_page_header = NULL;

static void *extend_heap();
void *split_page_sizeclass(void *bp, size_t size);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if (mem_heap_lo() > mem_heap_hi())
    {
        first_page_header = extend_heap();
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    void *cur_page_header = first_page_header;
    int idx = -3;
    char *header = NULL;
    char *bp = NULL;
    int asize = size;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        size = DSIZE;

    for (size--; size > 0; size /= 2)
        idx++;

    while (cur_page_header < mem_heap_hi())
    {
        header = cur_page_header + (DSIZE * idx);

        if (SUCC(header) != NULL)
        {
            bp = SUCC(header);
            SUCC(header) = SUCC(bp);
            return bp;
        }

        cur_page_header += PAGE_SIZE;
    }

    if ((cur_page_header = extend_heap()) == NULL)
        return NULL;

    header = cur_page_header + (DSIZE * idx);

    bp = SUCC(header);
    SUCC(header) = SUCC(bp);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    void *cur_page_header = first_page_header;
    void *cur_memblock;
    int idx;

    for (; cur_page_header < mem_heap_hi; cur_page_header += PAGE_SIZE)
        if (bp < cur_page_header + PAGE_SIZE)
            break;

    cur_memblock = cur_page_header + (DSIZE * FREE_LIST_LENGTH);
    for (idx = 0;; cur_memblock += CHUNKSIZE)
    {
        if (bp < cur_memblock + CHUNKSIZE)
            break;

        idx++;
    }

    char *header = cur_page_header + (DSIZE * idx);
    SUCC(bp) = SUCC(header);
    SUCC(header) = bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    // // 원래 size
    // size_t original_size = GET_SIZE(HDRP(bp));

    // // 새로운 size 크기만큼 할당
    // void *new_bp = mm_malloc(size);

    // // size 변화가 없으면 원래 bp return
    // if (new_bp == NULL)
    //     return bp;

    // // 새로 할당 받은 블록에 원래 data 옮김
    // memcpy(new_bp, bp, MIN(size, original_size));

    // // 원래 블록 반환
    // mm_free(bp);

    // // 새로운 블록 주소 return
    // return new_bp;
}

void *split_page_sizeclass(void *bp, size_t size)
{
    void *header = bp;

    for (;; bp = SUCC(bp))
    {
        if (bp + size == header + CHUNKSIZE)
        {
            SUCC(bp) = NULL;
            break;
        }
        else
            SUCC(bp) = bp + size;
    }

    return header;
}

static void *extend_heap()
{
    void *cur_page_header;
    void *memblock_header;
    void *header;

    if ((cur_page_header = mem_sbrk(PAGE_SIZE)) == (void *)-1)
        return NULL;

    memblock_header = cur_page_header + (FREE_LIST_LENGTH * DSIZE);

    for (int free_list_idx = 0; free_list_idx < FREE_LIST_LENGTH; free_list_idx++)
    {
        header = split_page_sizeclass(memblock_header + (CHUNKSIZE * free_list_idx), (8 << free_list_idx));
        INIT_POINTER(cur_page_header + (DSIZE * free_list_idx), header);
    }

    return cur_page_header;
}