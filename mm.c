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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

// size와 할당 비트를 합해서 header와 footer의 값을 계산
#define PACK(size, alloc) ((size) | (alloc))

// p가 참조하는 워드를 읽어서 return하거나 val값을 저장
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// header와 footer의 값을 보고 각각 size와 할당 비트를 return
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp : 블록 포인터
// header나 footer를 가리키는 포인터를 return
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PRED(bp) (*(void **)(bp))
#define SUCC(bp) (*(void **)(bp + WSIZE))

// 다음과 이전 블록의 블록 포인터를 각각 return
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 
 * mm_init - initialize the malloc package.
 */

// 항상 첫번째 사용가능한 블록을 가리키는 포인터
static char *free_list_header = NULL;

// 가용 블록 연결
static void *coalesce(void *bp)
{
    // 이전 블록과 다음 블록의 할당 비트
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    // 현재 블록의 size
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록과 다음 블록 모두 할당되어 있는 경우
    if (prev_alloc && next_alloc) return bp;

    // 다음 블록만 가용 블록인 경우
    else if (prev_alloc && !next_alloc) {
        // 다음 블록의 크기만큼 size에 더한다
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 바뀐 size로 현재 블록의 header와 footer 수정
        // 다음 블록의 footer을 바꿔야하지 않나? 
        //     -> 이미 합쳐져서 bp의 footer가 다음 블록의 footer와 동일
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 이전 블록만 가용 블록인 경우
    else if (!prev_alloc && next_alloc) {
        // 이전 블록의 크기만큼 size에 다한다
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));

        // 바뀐 size로 이전 블록의 header와 지금 블록의 footer를 수정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        // 현재 노드를 이전 노드로 바꿈
        void *origin_bp = bp;
        bp = PREV_BLKP(bp);

        PRED(bp) = NULL;
        SUCC(bp) = SUCC(origin_bp);
        free_list_header = bp;
    }

    // 이전 블록과 다음 블록 둘 다 가용 블록인 경우
    else {
        // 이전 블록의 크기와 다음 블록의 크기 만큼 size에 더한다
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        
        // 바뀐 size로 이전 블록의 header와 다음 블록의 footer를 수정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        // 현재 노드를 이전 노드로 바꿈
        void *origin_bp = bp;
        bp = PREV_BLKP(bp);

        // 이전 블록의 predecessor, 다음 블록의 successor 계승
        PRED(bp) = NULL;
        SUCC(bp) = SUCC(origin_bp);
        free_list_header = bp;
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 데이터 정렬을 유지하기 위해 홀수 개수의 words의 블록 크기 조정
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    // 가용 블록의 header와 footer 초기화
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));

    // 가용 블록의 prodecessor와 successor 초기화
    PRED(bp) = NULL;
    SUCC(bp) = NULL;

    // 이전 블록이 가용 블록이면 연결
    return coalesce(bp);
}

int mm_init(void)
{
    // heap_free_header 초기화
    if ((free_list_header = mem_sbrk(2 * WSIZE)) == (void *)-1) return -1;

    // header와 footer 초기화
    PUT(free_list_header, PACK(DSIZE, 0));
    PUT(free_list_header + (3 * WSIZE), PACK(DSIZE, 0));

    // predecessor와 successor 초기화   
    free_list_header += WSIZE;
    PRED(free_list_header) = NULL;
    SUCC(free_list_header) = NULL;

    // 성공 여부에 따라 return
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    return 0;
}

// first fit으로 가용 블록 탐색
static void *find_fit(size_t asize)
{
    // bp를 첫 가용 블록으로 초기화
    void *bp = free_list_header;

    // size가 0인 블록을 만나기 전까지 = epilogue를 만나기 전까지 = 가용 리스트 끝까지 갈 때까지
    while (bp != NULL) {
        // 현재 블록이 할당 받은 블록이거나 블록 size가 필요한 size보다 작으면 다음 블록으로 점프
        if (GET_SIZE(HDRP(bp)) < asize) bp = SUCC(bp);
        
        // 현재 블록이 필요한 size를 담을 수 있는 가용 블록이면 블록 주소 return
        else return bp;
    }

    // 현재 heap에 필요한 size를 담을 수 있는 가용 블록이 없으면 NULL return
    return NULL;
}

// 가용 블록에서 적당한 크기의 블록 할당
static void place(void *bp, size_t asize)
{
    // 가용 블록 전체 크기
    size_t csize = GET_SIZE(HDRP(bp));

    // 전체 크기에서 필요한 크기를 빼고 남은 크기
    size_t remain = csize - asize;

    // 남은 크기가 최소 블록 크기보다 작으면
    if (remain < (2 * DSIZE)) {
        // 전체 크기를 모두 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));

        // 가용 블록 연결 리스트에서 삭제
        SUCC(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);
    }

    // 남은 크기가 최소 블록 크기보다 크거나 같으면
    else {
        // 필요한 크기만큼 할당하고
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 가용 블록 연결 리스트에서 삭제
        SUCC(PRED(bp)) = SUCC(bp);
        PRED(SUCC(bp)) = PRED(bp);

        // 남은 크기를 가용블록으로 만듬
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(remain, 0));
        PUT(FTRP(bp), PACK(remain, 0));

        // 새로 생긴 가용 블록을 가용 블록 리스트 맨 앞에 연결
        PRED(bp) = NULL;
        SUCC(bp) = free_list_header;
        free_list_header = bp;
    }
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
    if (size == 0) return NULL;

    // 최소 asize = 16 = 2 * DSIZE = header(4) + footer(4) + payload(8)
    if (size <= DSIZE) asize = 2 * DSIZE;
    // size + (DSIZE - 1) -> size에 데이터 정렬에 맞춰 padding 부분 추가
    // + DSIZE -> header와 footer 블록
    else asize = DSIZE * ((size + (DSIZE - 1) + (DSIZE)) / DSIZE);

    // asize를 수용할 수 있는 가용 블록을 찾으면
    if ((bp = find_fit(asize)) != NULL) {
        // 메모리를 할당하고 bp return
        place(bp, asize);
        return bp;
    }

    // asize를 수용할 수 있는 가용 블록이 없으면
    // 추가해야하는 heap 크기
    extendsize = MAX(asize, CHUNKSIZE);

    // heap 추가 요청 실패시 NULL return
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    
    // heap 추가 요청 성공시 메모리를 할당하고 bp return
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

    // 새로 생긴 가용 블록을 가용 블록 리스트 맨 앞에 연결
    PRED(bp) = NULL;
    SUCC(bp) = free_list_header;
    free_list_header = bp;

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
    if (new_bp == NULL) return bp;

    // 새로 할당 받은 블록에 원래 data 옮김
    memcpy(new_bp, bp, MIN(size, original_size));

    // 원래 블록 반환
    mm_free(bp);

    // 새로운 블록 주소 return
    return new_bp;
}














