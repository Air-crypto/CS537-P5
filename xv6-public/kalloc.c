// Physical memory allocator, intended to allocate
// memory for user processes, kernel stacks, page table pages,
// and pipe buffers. Allocates 4096-byte pages.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "spinlock.h"

void freerange(void *vstart, void *vend);
extern char end[]; // first address after kernel loaded from ELF file
                   // defined by the kernel linker script in kernel.ld

struct run {
  struct run *next;
};

struct {
  struct spinlock lock;
  int use_lock;
  struct run *freelist;
} kmem;

static unsigned char ref_counts[PHYSTOP/PGSIZE];

// Initialization happens in two phases.
// 1. main() calls kinit1() while still using entrypgdir to place just
// the pages mapped by entrypgdir on free list.
// 2. main() calls kinit2() with the rest of the physical pages
// after installing a full page table that maps them on all cores.
void
kinit1(void *vstart, void *vend)
{
  initlock(&kmem.lock, "kmem");
  kmem.use_lock = 0;
  // Initialize all reference counts to 0
  memset(ref_counts, 0, sizeof(ref_counts));
  freerange(vstart, vend);
}

void
kinit2(void *vstart, void *vend)
{
  freerange(vstart, vend);
  kmem.use_lock = 1;
}

void
freerange(void *vstart, void *vend)
{
  char *p;
  p = (char*)PGROUNDUP((uint)vstart);
  for(; p + PGSIZE <= (char*)vend; p += PGSIZE)
    kfree(p);
}

int
get_ref_count(char *pa)
{
  return ref_counts[V2P(pa)/PGSIZE];
}

void
inc_ref_count(char *pa)
{
  if(ref_counts[V2P(pa)/PGSIZE] < 255)
    ref_counts[V2P(pa)/PGSIZE]++;
}

void
dec_ref_count(char *pa)
{
  if(ref_counts[V2P(pa)/PGSIZE] > 0)
    ref_counts[V2P(pa)/PGSIZE]--;
}

int
get_ref_count_locked(char *pa)
{
  int count;
  acquire(&kmem.lock);
  count = ref_counts[V2P(pa)/PGSIZE];
  release(&kmem.lock);
  return count;
}

void
inc_ref_count_locked(char *pa)
{
  acquire(&kmem.lock);
  if(ref_counts[V2P(pa)/PGSIZE] < 255)
    ref_counts[V2P(pa)/PGSIZE]++;
  release(&kmem.lock);
}

void
dec_ref_count_locked(char *pa)
{
  acquire(&kmem.lock);
  if(ref_counts[V2P(pa)/PGSIZE] > 0)
    ref_counts[V2P(pa)/PGSIZE]--;
  release(&kmem.lock);
}

//PAGEBREAK: 21
// Free the page of physical memory pointed at by v,
// which normally should have been returned by a
// call to kalloc().  (The exception is when
// initializing the allocator; see kinit above.)
void
kfree(char *v)
{
  struct run *r;

  if((uint)v % PGSIZE || v < end || V2P(v) >= PHYSTOP)
    panic("kfree");

  if(kmem.use_lock)
    acquire(&kmem.lock);

  // Decrease the reference count
  dec_ref_count(v);

  // Only free if reference count is zero
  if(get_ref_count(v) == 0) {
    // Fill with junk to catch dangling refs.
    memset(v, 1, PGSIZE);

    r = (struct run*)v;
    r->next = kmem.freelist;
    kmem.freelist = r;
  }

  if(kmem.use_lock)
    release(&kmem.lock);
}

// Allocate one 4096-byte page of physical memory.
// Returns a pointer that the kernel can use.
// Returns 0 if the memory cannot be allocated.
char*
kalloc(void)
{
  struct run *r;

  if(kmem.use_lock)
    acquire(&kmem.lock);
  r = kmem.freelist;
  if(r) {
    kmem.freelist = r->next;

    // Initialize reference count
    ref_counts[V2P((char*)r)/PGSIZE] = 1;

    if(kmem.use_lock)
      release(&kmem.lock);

    // Fill with junk to catch uninitialized usage.
    memset((char*)r, 5, PGSIZE);
  } else {
    if(kmem.use_lock)
      release(&kmem.lock);
  }
  return (char*)r;
}

