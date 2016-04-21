/*
Features included:
-Bidirectional Coalescing to make for better utilization
-Made sure there are no free blocks next to each other
-There won't be space that cannot be used again
-First free list has block size of two times minimum block size (arbitrary number)

Block structure:
SIZET bytes as header, followed by information, followed by SIZET bytes of footer.
Last bits of header/footer: flags
Flag rules:
0 free, 1 allocated

We choose to make two blocks of a particular size when there is not a free block of that size because 
it will make it more efficient to search for another block of the similar size. Then the second block 
is returned. Time used to extend the heap is then saved.

*More information about each function can be seen in comments before the function*
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
    "The A Team",
    /* First member's full name */
    "Chung Ho Lee",
    /* First member's email address */
    "chunglee2018@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Vyas Alwar",
    /* Second member's email address (leave blank if none) */
    "VyasAlwar2018@u.northwestern.edu"
};


#define ALIGNMENT 8 //Alignment
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) //Alignment Rules
#define PT_SIZE (ALIGN(sizeof(void *))) //Common Alignment
#define SIZET (ALIGN(sizeof(size_t))) //Common Alignment
#define MINBLK (2*(SIZET + PT_SIZE)) //Minimum allowed block
#define COMBINE(size, alloc) ((size) | (alloc)) // Combines allocation bit and the size
#define BLOCK_WIDTH(p) (HDER(p) & ~0x3) //Components of a header
#define BK_ALC(p) (HDER(p) & 0x3) //Components of a header
#define HDER(p) (*((size_t *)p)) //Header of a block
#define FTER(p) (*((size_t *)((char *)p + BLOCK_WIDTH(p) - SIZET))) //Footer of a block
#define PREV(p) (*((void **)((char *)p + PT_SIZE + SIZET ))) // Acceses previous block in free list
#define NEXT(p) (*((void **)((char *)p + SIZET))) // Acceses next block in free list

//Other helpful functions
static void mm_placing(void *dest, void *bp);
static void mm_removing(void *bp);
static void mm_sethderfter(void *bp, size_t value);
static void mm_organize(void *ptr);
static void *mm_searchfree(size_t nsz);
static void *mm_blocktoheap(void *ptr);

// Initialize malloc, makes root that gives access to free lists
int mm_init(void)
{
	size_t rbsize = MINBLK + SIZET*(sizeof(size_t) * 8 - 6);
	if (mem_sbrk(rbsize) == (void *) - 1)
	{
		return -1;
	}
	int i;
	//cannot declare int inside for loop
	for (i = 0; i < (sizeof(size_t) * 8 - 5); i++)
	{
		NEXT(((void *)((char *)mem_heap_lo() + SIZET * i))) = NULL;
	}
	mm_sethderfter(mem_heap_lo(), COMBINE(rbsize, 0x2));
	return 0;
}

// Returns pointer to block, may split block
void *mm_malloc(size_t size)
{
	size_t nsize = ALIGN(size + SIZET * 2);
	if (nsize < MINBLK)
	{
		nsize = MINBLK;
	}
	void *found = mm_searchfree(nsize);
	if (found == NULL)
	{
		return NULL;
	}

	mm_removing(found);

	size_t tsize = BLOCK_WIDTH(found) - nsize;
	if (tsize < MINBLK)
	{
		mm_sethderfter(found, COMBINE(BLOCK_WIDTH(found), 0x1));
	}
	else
	{
		mm_sethderfter(found, COMBINE(nsize, 0x1));
		void *tail = ((void *)((char *)found + BLOCK_WIDTH(found)));
		// Accesses the next block
		mm_sethderfter(tail, COMBINE(tsize, 0x0));
		mm_organize(tail);
	}

	return ((void *)((char *)(found)+SIZET));
}

// Frees a block
void mm_free(void *pd)
{
	void *bp = ((void *)((char *)pd - SIZET));
	mm_sethderfter(bp, COMBINE(BLOCK_WIDTH(bp), 0x0));
	bp = mm_blocktoheap(bp);
}

// Returns pointer to allocated region
void *mm_realloc(void *p, size_t s)
{
	void *op = p;
	void *np;
	size_t csz;
	np = mm_malloc(s);
	if (np == NULL)
	{
		return NULL;
	}
	csz = *(size_t *)((char *)op - SIZET);
	if (s < csz)
	{
		csz = s;
	}
	memcpy(np, op, csz);
	mm_free(op);
	return np;
}

//Find free block of nsz or bigger
static void *mm_searchfree(size_t nsz)
{
	int i = 0;
	void *rval = NULL;

	// Calculates and saves the first free list that should fit nsz
	while ((0x40 * (1 << i)) <= nsz)
	{
		i++;
	}

	int first = i;

	while (i < (sizeof(size_t) * 8 - 5))
	{
		if (NEXT(((void *)((char *)mem_heap_lo() + SIZET * i))) != NULL)
		{
			void *root = ((void *)((char *)mem_heap_lo() + SIZET * i));
			void *bp = NEXT(root);
			void *found = NULL;
			while (bp != NULL && found == NULL)
			{
				if (BLOCK_WIDTH(bp) >= nsz)
				{
					found = bp;
				}
				bp = NEXT(bp);
			}
			rval=found;
		}

		if (rval != NULL)
		{
			return rval;
		}
		i++;
	}

	void *root = ((void *)((char *)mem_heap_lo() + SIZET * first));
	void *hpt = ((void *)((char *)(mem_heap_hi() + 1) - (*((size_t *)((char *)(mem_heap_hi() + 1) - SIZET)) & ~0x3)));
	// Accesses the previous block
	void *found;

	// Adjusts heap to fit block, if there is a free block, add and return
	if (BK_ALC(hpt) == 0x0)
	{
		size_t ext = nsz - BLOCK_WIDTH(hpt);
		found = mem_sbrk(ext);
		if (found == (void *)-1)
		{
			return NULL;
		}
		mm_sethderfter(found, COMBINE(ext, 0x0));
		found = mm_blocktoheap(found);
	}

	//Else, allocate two blocks of size, return top block
	else
	{
		void *ext = mem_sbrk(nsz);
		if (ext == (void *)-1)
		{
			return NULL;
		}
		mm_sethderfter(ext, COMBINE(nsz, 0x0));
		mm_placing(root, ext);
		found = mem_sbrk(nsz);
		if (found == (void *)-1)
		{
			return NULL;
		}
		mm_sethderfter(found, COMBINE(nsz, 0x0));
		mm_placing(root, found);
	}
	return found;
}

//Returns pointer to input block
//Place a floating block in heap, defined for floating blocks.

static void *mm_blocktoheap(void *bp)
{
	void *next = ((void *)((char *)bp + BLOCK_WIDTH(bp)));
	// Accesses the next block
	void *prev = ((void *)((char *)bp - (*((size_t *)((char *)bp - SIZET)) & ~0x3)));
	// Accesses the previous block

	if (next < mem_heap_hi() + 1 && BK_ALC(next) == 0x0)
	{
		mm_removing(next);
		mm_sethderfter(bp, COMBINE(BLOCK_WIDTH(bp) + BLOCK_WIDTH(next), 0x0));
	}
	if (BK_ALC(prev) == 0x0)
	{
		mm_removing(prev);
		mm_sethderfter(prev, COMBINE(BLOCK_WIDTH(prev) + BLOCK_WIDTH(bp), 0x0));
		mm_organize(prev);
		return prev;
	}
	else
	{
		mm_organize(bp);
		return bp;
	}
}

// Puts block in the right list
static void mm_organize(void *p)
{
	int i = 0;
	while ((0x40 * (1 << i)) <= BLOCK_WIDTH(p))
	{
		i++;
	}
	mm_placing(((void *)((char *)mem_heap_lo() + SIZET * i)), p);
}

//Sets the header and footer of a block to value
//Header is set first
static void mm_sethderfter(void *p, size_t input)
{
	HDER(p) = input;
	FTER(p) = input;
}

// Inserts block after another
static void mm_placing(void *loc, void *p)
{
	PREV(p) = loc;
	NEXT(p) = NEXT(loc);
	if (NEXT(loc) != NULL)
	{
		PREV(NEXT(loc)) = p;
	}
	NEXT(loc) = p;
}

// Removes free block
static void mm_removing(void *p)
{
	NEXT(PREV(p)) = NEXT(p);
	if (NEXT(p) != NULL)
	{
		PREV(NEXT(p)) = PREV(p);
	}
}













