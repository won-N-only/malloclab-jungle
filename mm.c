/* mm-naive.c - The fastest, least memory-efficient malloc package.
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free. */
/* NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * okok let go */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// team - info
team_t team = {
    // Team name //
    "team 932",
    // First member's full name //
    "jayK",
    // First member's email address //
    "jayK.com",
    "",
    ""};

////////////////////////////변수시작/////////////////////////////////////

// // global vars//
// static char *mem_strt;     // 메모리 시작 주소
// static char *mem_brk;      // 메모리 끝 주소 +1
// static char *mem_max_addr; // 최대 유효 힙 주소 + 1

// 전처리기 매크로 할당
#define wsize 4                           // 워드는 4바이트
#define dsize 8                           // 더블워드는 8바이트
#define chunksize (1 << 6)                // 청크 하나에 4KB할당(페이지 크기랑 일치해서 편할듯)
#define max(x, y) ((x) > (y) ? (x) : (y)) // x,y중 max값

// 크기와 가용여부를 합쳐서(비트연산 활용) 표시함
#define pack(size, alloc) ((size) | (alloc)) // or연산으로 헤더에서 쓸 word만들어줌

// 주소p에 r/w
#define get(p) (*(unsigned int *)(p))                     // 포인터로 주소p를 참조, 블록 이동할 때 쓸거
#define put(p, val) (*(unsigned int *)(p)) = ((int)(val)) // 주소 p에 val이라는 주소를 담음

// 주소p에서 크기와 할당여부를 읽어옴
#define get_size(p) (get(p) & ~0x7) // &와 ~를 이용해 뒷 3자리를 제외한 비트를 가져옴
#define get_alloc(p) (get(p) & 0x1) // 0번째 비트(할당여부)를 가져옴

//(char*)인 이유는 1바이트 단위로 조작이 가능해서임
#define header_of(bp) ((char *)(bp)-wsize)                             // header 포인터
#define footer_of(bp) ((char *)(bp) + get_size(header_of(bp)) - dsize) // FooTer 포인터
#define next_block(bp) ((char *)(bp) + get_size((char *)(bp)-wsize))   // 다음블럭으로 ㄱㄱ
#define prev_block(bp) ((char *)(bp)-get_size((char *)(bp)-dsize))     // 이전블록으로 ㄲㄲ

// 힙 포인터 설정(전역으로 해야함)
static char *heap_listp;

// next_fit을 위함/ 가장 최근 할당 위치 전역변수화
static char *last_allocated = NULL;

// best_fit을 위함/ fittest한 위치 저장
static char *best_address = NULL;

// #define ALIGNMENT 8 // single word (4) or double word (8) alignment //

// // rounds up to the nearest multiple of ALIGNMENT //
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

////////////////////////////함수선언/////////////////////////////////////
int mm_init(void);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static char *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);
static char *best_fit(size_t asize);

////////////////////////////함수시작/////////////////////////////////////

// 힙 초기화
int mm_init(void)
{
    // mem_sbrk word 4개만큼 늘림, ==로 overflow아닌지 검사
    if ((heap_listp = mem_sbrk(4 * wsize)) == (void *)-1)
        return -1;

    put(heap_listp, 0); // 블록 생성할때 word 1개 만큼 패딩,

    // 여기부터 Double Word 사용
    put(heap_listp + (1 * wsize), pack(dsize, 1)); // 그 다음칸에 pro-헤더
    put(heap_listp + (2 * wsize), pack(dsize, 1)); // 그 다음칸에 pro-푸터
    put(heap_listp + (3 * wsize), pack(dsize, 1)); // 그 다음칸에 epi-헤더
    //
    heap_listp += (2 * wsize); // 포인터 pro-헤더와 pro-푸터 사이로 이동

    if (extend_heap(chunksize / wsize) == NULL) // 힙 최초 설정
        return -1;

    return 0;
}

// heap 확장함(sbrk처럼), 인수 words인거 확인
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size; // unsigned int

    // 더블워드 정렬위해 짝수로 만들어서 alloc
    size = (words % 2) ? (words + 1) * wsize : words * wsize;
    if ((int /*원래 long임*/)(bp = mem_sbrk(size)) == -1) // heap크기 size만큼 늘리고 bp 이동시킴. 그 후 long으로 변환
        return NULL;                                      // 사이즈를 늘릴 때마다 old brk 원래 sbrk로 갱신(함수 내부 참조)

    // 생성한 free-heap space에 헤더, 푸터만들고 에필로그헤더 갱신
    put(header_of(bp), pack(size, 0));
    put(footer_of(bp), pack(size, 0));
    put(header_of(next_block(bp)), pack(0, 1));

    // 만든 free space를 주변 블록과 합쳐줌
    return coalesce(bp);
}

////////////////////////////coalesce/////////////////////////////////////
static void *coalesce(void *bp) // 앞 뒤 가용블럭과 free한 블럭 합칩
{
    // 앞 뒤 블럭의 free 여부 확인
    size_t prev_alloc = get_alloc(footer_of(prev_block(bp)));
    size_t next_alloc = get_alloc(header_of(next_block(bp)));
    size_t size = get_size(header_of(bp));

    // 둘다 alloc이면 넘어감
    if (prev_alloc && next_alloc)
        return bp;

    // 앞뒤 중 가용상태인것과 합쳐줌
    else if (prev_alloc && !next_alloc) // 다음 블럭이 가용일때
    {
        size += get_size(header_of(next_block(bp)));
        put(header_of(bp), pack(size, 0));
        put(footer_of(bp), pack(size, 0)); // 헤더 먼저 해줘서 다음블럭의 footer 가리킴
        last_allocated = bp;               // next_fit의 last alloc 갱신
    }
    else if (!prev_alloc && next_alloc) // 이전 블록이 가용일때
    {
        size += get_size(header_of(prev_block(bp)));
        put(footer_of(bp), pack(size, 0));
        put(header_of(prev_block(bp)), pack(size, 0)); // prev의 헤더에 put
        bp = prev_block(bp);                           // bp를 원 prev의 헤더로 옮김
        last_allocated = bp;                           // next_fit의 last alloc 갱신
    }
    else // 둘 다 가용일때
    {
        size += get_size(header_of(prev_block(bp))) + get_size(footer_of(next_block(bp)));
        put(header_of(prev_block(bp)), pack(size, 0));
        put(footer_of(next_block(bp)), pack(size, 0));
        bp = prev_block(bp);
        last_allocated = bp; // next_fit의 last alloc 갱신
    }
    return bp;
}
////////////////////////////coalesce/////////////////////////////////////

// 메모리 할당해줌
void *mm_malloc(size_t size)
{
    size_t asize;       // 블록 사이즈 조정(adjust)
    size_t extend_size; // fit없으면 extend로 넘기기 위한 var
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= dsize)     // malloc받은 사이즈가 작아서 헤더푸터 안들어가면
        asize = 2 * dsize; // asize에 헤더푸터 사이즈(16Byte) 넣음
    else                   // 무조건 자기보다 큰 8의 배수 중 가장 작은값으로 바꿈
        asize = dsize * ((size + (dsize) + (dsize - 1)) / dsize);

    ////////////////////////////TEST/////////////////////////////////////
    // bp = find_fit(asize); // asize 정하고나서 bp에 반영함
    bp = next_fit(asize); // asize 정하고나서 bp에 반영함

    if (bp != NULL) // fit to asize 찾아서 place
    {
        place(bp, asize);
        return bp;
    }
    ////////////////////////////TEST/////////////////////////////////////

    // if통과 못하면 size extend해주고 다시 place
    extend_size = max(asize, chunksize); // chunksize=4KB(initial val)
    if ((bp = extend_heap(extend_size / wsize)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) // 어떻게 fit한곳 찾냐면 first fit
{
    void *bp;
    for (bp = heap_listp; get_size(header_of(bp)) > 0; bp = next_block(bp))
    { // header of next bp가 0이되면 끝
        if (!get_alloc(header_of(bp)) && (asize <= get_size(header_of(bp))))
            return bp; // alloc이 0이고 size가 asize보다 크면 return 해당 bp
    }
    return NULL; // NULL이면 fit이없음, extend_size 실행
}

// next_fit 메모리 할당 함수
static char *next_fit(size_t asize)
{
    char *start = last_allocated;
    char *bp;

    // 처음 검색 시작 위치 설정
    if (last_allocated == NULL)
        start = heap_listp;

    // last_allocated에서 힙의 끝까지 검색
    for (bp = start; get_size(header_of(bp)) > 0; bp = next_block(bp)) // epi-헤더만나면 size=0이라 for문끝
    {
        if (!get_alloc(header_of(bp)) && asize <= get_size(header_of(bp)))
        {
            last_allocated = bp;
            return bp;
        }
    }
    // 가용 없으면 힙의 시작부터 last_allocated까지 다시 검색
    for (bp = heap_listp; bp < start; bp = next_block(bp))
    {
        if (!get_alloc(header_of(bp)) && asize <= get_size(header_of(bp)))
        {
            last_allocated = bp;
            return bp;
        }
    }
    return NULL; // heap내에 가용 없으면 extend를 위해 NULL 반환;
}
static char *best_fit(size_t asize)
{
    char *start = best_address;
    char *bp;

    // 처음부터 힙의 끝까지 검색
    for (bp = heap_listp; get_size(header_of(bp)) > 0; bp = next_block(bp)) // epi-헤더만나면 size=0이라 for문끝
    {
        if (!get_alloc(header_of(bp)) && asize <= get_size(header_of(bp)))
        {
            best_address = bp;
            if (bp < best_address)
                best_address = bp;
        }
        return bp;
    }

    return NULL; // heap내에 가용 없으면 extend를 위해 NULL 반환;
}

static void place(void *bp, size_t asize) // find한 bp, asize 넣어서 place해줌
{
    size_t curr_size = get_size(header_of(bp));
    if ((curr_size - asize) >= (2 * dsize)) // 현재 size-받은 size해서 헤더+푸터size보다 크면
    {
        put(header_of(bp), pack(asize, 1));             // asize만큼 떨어진 헤더 푸터
        put(footer_of(bp), pack(asize, 1));             // 둘다 채우고
        bp = next_block(bp);                            // 다음블럭으로 가서
        put(header_of(bp), pack(curr_size - asize, 0)); // 남은 부분 헤더 푸터 만들어줌
        put(footer_of(bp), pack(curr_size - asize, 0));
    }
    else // 헤더 푸터 못들어가는 곳이면 그냥 curr 다 채움
    {
        put(header_of(bp), pack(curr_size, 1));
        put(footer_of(bp), pack(curr_size, 1));
    }
}

// free하고 헤더푸터에 f표현 + coalesce해줌
// chunk size넘어가면? 어떻게해 8000인데 4000만 쓰고있으면?
void mm_free(void *bp)
{
    size_t size = get_size(header_of(bp));
    put(header_of(bp), pack(size, 0));
    put(footer_of(bp), pack(size, 0));
    coalesce(bp);
}

////////////////////////////re-alloc/////////////////////////////////////
//  - 이미 할당한 공간의 크기를 바꿀 때 realloc 함수를 사용한다.
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0) // realloc 하려는 size 0이하면 free
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL) // heap 없을때 malloc으로 해줌
        return mm_malloc(size);

    void *new_bp = mm_malloc(size);

    if (new_bp == NULL) // 힙이 꽉 찼을때
        return 0;

    size_t oldsize = get_size(header_of(bp));

    if (size < oldsize)
        oldsize = size;

    memcpy(new_bp, bp, oldsize);
    mm_free(bp);

    return new_bp;
}
// dd