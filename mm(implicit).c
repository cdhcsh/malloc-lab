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

// #define FIRST_FIT
#define NEXT_FIT
// #define BEST_FIT

/* 함수 프로토타입 선언*/
static void *_extend_heap(size_t words);
static void *_coalesce(void *p);
static char *_find_fit(size_t size);
static void _place(void *p, size_t size);

static char *heap_listp; /* prologue 를 가리킴*/

#ifdef NEXT_FIT
static void *next_p;
#endif

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

static void *_coalesce(void *p)
{
    /*
    case 1: 이전과 다음 블록 모두 할당된 상태 -> 통합 종료
    case 2: 이전 블록은 할당되있고 다음블록은 가용상태 -> 현재 블록을 다음 리스트와 연결함
    case 3: 이전 블록은 가용상태, 다음블록은 할당상태 -> 현재 블록을 이전 리스트와 연결함
    case 4: 이전과 다음 블록 모두 가용상태 -> 이전,현재,다음 블록을 연결
    */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(p)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
    size_t size = GET_SIZE(HDRP(p));

    if (prev_alloc && next_alloc)
    { // case 1
        return p;
    }
    else if (prev_alloc && !next_alloc)
    { // case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(p)));
        PUT(HDRP(p), PACK(size, 0));
        PUT(FTRP(p), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // case 3
        size += GET_SIZE(HDRP(PREV_BLKP(p)));
        PUT(FTRP(p), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(p)), PACK(size, 0));
        p = PREV_BLKP(p);
    }
    else
    { // case 4
        size += GET_SIZE(FTRP(NEXT_BLKP(p))) + GET_SIZE(HDRP(PREV_BLKP(p)));
        PUT(HDRP(PREV_BLKP(p)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(p)), PACK(size, 0));
        p = PREV_BLKP(p);
    }
#ifdef NEXT_FIT
    next_p = p; // next_fit
#endif
    return p;
}

static char *_find_fit(size_t size)
{
#ifdef FIRST_FIT
    /* first fit*/
    void *p;
    for (p = heap_listp; GET_SIZE(HDRP(p)) > 0; p = NEXT_BLKP(p))
    {
        if (!GET_ALLOC(HDRP(p)) && (size <= GET_SIZE(HDRP(p))))
        {
            return p;
        }
    }
    return NULL;
#endif

#ifdef NEXT_FIT
    /* next fit*/
    void *p;
    for (p = next_p; GET_SIZE(HDRP(p)) > 0; p = NEXT_BLKP(p))
    {
        if (!GET_ALLOC(HDRP(p)) && (size <= GET_SIZE(HDRP(p))))
        {
            next_p = p;
            return p;
        }
    }
    for (p = heap_listp; p != next_p; p = NEXT_BLKP(p))
    {
        if (!GET_ALLOC(HDRP(p)) && (size <= GET_SIZE(HDRP(p))))
        {
            next_p = p;
            return p;
        }
    }
    return NULL;
#endif

#ifdef BEST_FIT
    /* best fit*/
    void *p;
    void *min_p;
    for (p = min_p = heap_listp; GET_SIZE(HDRP(p)) > 0; p = NEXT_BLKP(p))
    {
        if (!GET_ALLOC(HDRP(p)) && (size <= GET_SIZE(HDRP(p))))
        {
            if (GET_ALLOC(HDRP(min_p)) || GET_SIZE(HDRP(min_p)) > GET_SIZE(HDRP(p)))
            {
                min_p = p;
            }
        }
    }

    if (GET_ALLOC(HDRP(min_p)))
        return NULL;
    return min_p;
#endif
}
static void _place(void *p, size_t size)
{
    size_t c_size = GET_SIZE(HDRP(p)); // 현재 블록의 크기

    if ((c_size - size) >= (2 * DSIZE))
    { /* 할당 후 남은 공간이 최소 블록 크기 이상이라면 분할함*/
        PUT(HDRP(p), PACK(size, 1));
        PUT(FTRP(p), PACK(size, 1));
        p = NEXT_BLKP(p);
        PUT(HDRP(p), PACK(c_size - size, 0));
        PUT(FTRP(p), PACK(c_size - size, 0));
    }
    else
    {
        PUT(HDRP(p), PACK(c_size, 1));
        PUT(FTRP(p), PACK(c_size, 1));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignemt padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header -PACK(block size, alloc)*/
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer -PACK(block size, alloc)*/
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header -end*/
    heap_listp += (2 * WSIZE);

#ifdef NEXT_FIT
    next_p = heap_listp; // next_fit
#endif

    if (_extend_heap(CHUNKSIZE / WSIZE) == NULL)
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
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *p)
{
    size_t size = GET_SIZE(HDRP(p));

    PUT(HDRP(p), PACK(size, 0)); /* 가용 블록으로 변경 -header의 내용이 아니라 size라서 하위 3비트는 0임 */
    PUT(FTRP(p), PACK(size, 0));

#ifdef NEXT_FIT
    next_p = _coalesce(p); // next_fit
#else
#endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *p, size_t size)
{
    if ((int)size < 0)
        return NULL;
    else if ((int)size == 0)
    {
        mm_free(p);
        return NULL;
    }
    else if (size > 0)
    {
        size_t oldsize = GET_SIZE(HDRP(p));
        size_t newsize = size + 2 * WSIZE;
        if (newsize <= oldsize)
        {
            return p;
        }
        else
        {
            size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(p)));
            size_t csize;
            if (!next_alloc && ((csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(p))))) >= newsize)
            {
                PUT(HDRP(p), PACK(csize, 1));
                PUT(FTRP(p), PACK(csize, 1));
#ifdef NEXT_FIT
                next_p = p;
#endif
                return p;
            }
            else
            {
                void *new_ptr = mm_malloc(newsize);
                _place(new_ptr, newsize);
                memcpy(new_ptr, p, newsize);
                mm_free(p);
                return new_ptr;
            }
        }
    }
    else
        return NULL;
}
