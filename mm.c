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
    "team 7",
    /* First member's full name */
    "Donghwan Choi",
    /* First member's email address */
    "cdhcsh@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/*====================================================================================================*/
/*=========================== BASIC MACROS ============================================================*/
/*====================================================================================================*/

/* 기본 사이즈 지정*/
#define WSIZE 4             /* 워드와 header,footer 사이즈 (bytes)*/
#define DSIZE 8             /* double word (bytes) */
#define CHUNKSIZE (1 << 12) /* 확장될 힙의 크기 (bytes)*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 사이즈와 할당 비트 입력*/
#define PACK(size, alloc) ((size) | (alloc))

/* p의 주소값을 읽거나 씀*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* GET_SIZE : header,footer 로부터 사이즈를 읽음 */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* GET_ALLOC : header,footer 로부터 할당비트를 읽음*/
#define GET_ALLOC(p) (GET(p) & 0x1)

/* HDRP : 주소 p의 header를 가리키는 포인터 반환*/
#define HDRP(p) ((char *)(p)-WSIZE)
/* FTRP : 주소 p의 footer를 가리키는 포인터 반환*/
#define FTRP(p) ((char *)(p) + GET_SIZE(HDRP(p)) - DSIZE)

/* NEXT_BLKP : 다음 블록의 블록 포인터 반환*/
#define NEXT_BLKP(p) ((char *)(p) + GET_SIZE(HDRP(p)))
/* PREV_BLKP : 이전 블록의 블록 포인터 반환*/
#define PREV_BLKP(p) ((char *)(p)-GET_SIZE(((char *)(p)-DSIZE)))

/* 다음 가용 블록의 주소*/
#define GET_SUCC(p) (*(void **)((char *)(p) + WSIZE))
/* 이전 가용 블록의 주소*/
#define GET_PRED(p) (*(void **)(p))

/*====================================================================================================*/
/*=========================== FUNCTION PROTOTYPES ====================================================*/
/*====================================================================================================*/

/* 함수 프로토타입 선언*/
static void *_extend_heap(size_t words);
static void *_coalesce(void *p);
static char *_find_fit(size_t size);
static void _place(void *p, size_t size);
static void _remove_free_block(void *p);
static void _add_free_block(void *p);

/*====================================================================================================*/
/*=========================== EXTERNS VARIABLES ====================================================*/
/*====================================================================================================*/

static char *heap_listp; /* prologue 를 가리킴*/

/*====================================================================================================*/
/*=========================== SUB FUNCTIONS ==========================================================*/
/*====================================================================================================*/

/* 힙 확장*/
static void *_extend_heap(size_t words)
{
    char *p;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(p = mem_sbrk(size)) == -1) //
        return NULL;

    PUT(HDRP(p), PACK(size, 0));         /* Free block header */
    PUT(FTRP(p), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(p)), PACK(0, 1)); /* New epilogue header -새로운 끝 설정 */

    return _coalesce(p);
}

/* 블록 할당 해제*/
static void *_coalesce(void *p)
{
    /*
    case 1: 이전과 다음 블록 모두 할당된 상태 -> 통합 종료
    case 2: 이전 블록은 할당되있고 다음블록은 가용상태 -> 현재 블록을 다음 리스트와 연결함
    case 3: 이전 블록은 가용상태, 다음블록은 할당상태 -> 현재 블록을 이전 리스트와 연결함
    case 4: 이전과 다음 블록 모두 가용상태 -> 이전,현재,다음 블록을 연결
    */

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(p))) || (PREV_BLKP(p) == p);
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
    size_t size = GET_SIZE(HDRP(p));

    if (prev_alloc && next_alloc)
    { // case 1
        _add_free_block(p);
        return p;
    }
    else if (prev_alloc && !next_alloc)
    { // case 2
        _remove_free_block(NEXT_BLKP(p));
        size += GET_SIZE(HDRP(NEXT_BLKP(p)));
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // case 3
        size += GET_SIZE(HDRP(PREV_BLKP(p)));
        _remove_free_block(PREV_BLKP(p));
        p = PREV_BLKP(p);
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    else
    { // case 4
        size += GET_SIZE(FTRP(NEXT_BLKP(p))) + GET_SIZE(HDRP(PREV_BLKP(p)));
        _remove_free_block(NEXT_BLKP(p));
        _remove_free_block(PREV_BLKP(p));
        p = PREV_BLKP(p);
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    _add_free_block(p);
    return p;
}

/* 가용블록 연결 리스트 확인 */
static char *_find_fit(size_t size)
{
    /* BSET FIT*/
    void *p;
    void *best_fit = NULL;
    size_t min_remaining = 1 << 21;

    for (p = heap_listp; GET_ALLOC(HDRP(p)) == 0; p = GET_SUCC(p))
    {
        if (size <= (size_t)GET_SIZE(HDRP(p)))
        {
            size_t remaining = (size_t)GET_SIZE(HDRP(p)) - size;
            if (remaining < min_remaining)
            {
                min_remaining = remaining;
                best_fit = p;
            }
        }
    }
    return best_fit;
}
/* 가용블록 연결 리스트에 p 블록을 제거*/
static void _remove_free_block(void *p)
{
    if (GET_PRED(p) != NULL)
        GET_SUCC(GET_PRED(p)) = GET_SUCC(p);
    else
        heap_listp = GET_SUCC(p);
    GET_PRED(GET_SUCC(p)) = GET_PRED(p);
}

/* 가용블록 연결 리스트에 p 블록을 추가*/
static void _add_free_block(void *p)
{
    GET_SUCC(p) = heap_listp;
    GET_PRED(heap_listp) = p;
    GET_PRED(p) = NULL;
    heap_listp = p;
}

/* 가용블럭에 size만큼 할당 */
static void _place(void *p, size_t size)
{
    size_t c_size = GET_SIZE(HDRP(p)); // 현재 블록의 크기

    _remove_free_block(p); // 가용블록 연결 리스트에서 제거

    if ((c_size - size) >= (2 * DSIZE))
    { /* 할당 후 남은 공간이 최소 블록 크기 이상이라면 분할함*/
        PUT(HDRP(p), PACK(size, 1));
        PUT(FTRP(p), PACK(size, 1));

        p = NEXT_BLKP(p);

        PUT(HDRP(p), PACK(c_size - size, 0));
        PUT(FTRP(p), PACK(c_size - size, 0));
        _coalesce(p);
    }
    else
    {
        PUT(HDRP(p), PACK(c_size, 1));
        PUT(FTRP(p), PACK(c_size, 1));
    }
}
/*====================================================================================================*/
/*=========================== FUNCTIONS ==============================================================*/
/*====================================================================================================*/

/*
 * mm_init : heap_listp 초기 설정
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 header */
    heap_listp += (2 * WSIZE);                     /* 프롤로그 footer p*/

    if (_extend_heap(4) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc : 주어진 size를 가진 payload의 주소 반환
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *p;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE; /* size는 실제로 사용할 데이터 영역의 크기만 지정 -> 헤더, 풋터 포함하려고 더블워드 2배*/
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((p = _find_fit(asize)) != NULL)
    {
        _place(p, asize); /* 요청 블록 배치 */
        return p;
    }

    /* 맞는 블록이 없으면 힙 영역을 확장하고 요청 블록을 새 가용 블록에 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((p = _extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    _place(p, asize);
    return p;
}

/*
 * mm_free : 주소 p의 할당된 메모리 반환
 */
void mm_free(void *p)
{
    size_t size = GET_SIZE(HDRP(p));

    PUT(HDRP(p), PACK(size, 0)); /* 가용 블록으로 변경 -header의 내용이 아니라 size라서 하위 3비트는 0임 */
    PUT(FTRP(p), PACK(size, 0));
    _coalesce(p);
}

/*
 * mm_realloc : 주소 p의 할당된 블록의 크기를 size 만큼 변경하여 payload의 주소를 반환
 */
void *mm_realloc(void *p, size_t size)
{
    if (size <= 0)
    {
        mm_free(p);
        return 0;
    }
    if (p == NULL)
        return mm_malloc(size);

    size_t new_size = size + 2 * WSIZE;
    size_t old_size = GET_SIZE(HDRP(p));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(p)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(p)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(p)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
    size_t c_size;

    if (new_size <= old_size)
        return p;
    if (!prev_alloc && new_size <= (c_size = old_size + prev_size)) // 이전 블록과 통합
    {
        char *pre = PREV_BLKP(p);
        _remove_free_block(pre);
        memmove(pre, p, old_size);
        PUT(HDRP(pre), PACK(c_size, 1));
        PUT(FTRP(pre), PACK(c_size, 1));
        return pre;
    }
    if (!next_alloc && new_size <= (c_size = old_size + next_size)) // 다음 블록과 통합
    {
        _remove_free_block(NEXT_BLKP(p));

        PUT(HDRP(p), PACK(c_size, 1));
        PUT(FTRP(p), PACK(c_size, 1));
        return p;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return 0;
    memcpy(newptr, p, old_size);
    mm_free(p);
    return newptr;
}
