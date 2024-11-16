#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
void
mark_parent_pages_cow(pde_t *pgdir, uint sz)
{
  pte_t *pte;
  uint i;

  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, (void *) i, 0)) == 0)
      panic("mark_parent_pages_cow: pte should exist");
    if(!(*pte & PTE_P))
      continue;
    uint flags = PTE_FLAGS(*pte);
    if(flags & PTE_W){
      *pte &= ~PTE_W;    // Clear the writable flag
      *pte |= PTE_COW;   // Set the copy-on-write flag
    }
  }

  // Flush the TLB to ensure the CPU uses the updated PTEs
  lcr3(V2P(pgdir));
}


int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0)
    return -1;

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  // Copy file descriptors and current working directory.
  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  // Copy memory mappings from parent to child
  memmove(np->maps, curproc->maps, sizeof(curproc->maps));

  // Set up page table entries for mapped regions
  for(i = 0; i < MAX_WMMAP_INFO; i++){
    if(np->maps[i].valid){
      uint addr = np->maps[i].addr;
      uint length = np->maps[i].length;
      uint a = PGROUNDDOWN(addr);
      uint last = PGROUNDDOWN(addr + length - 1);

      for(; a <= last; a += PGSIZE){
        pte_t *pte_parent = walkpgdir(curproc->pgdir, (char*)a, 0);
        pte_t *pte_child = walkpgdir(np->pgdir, (char*)a, 1); // Allocate page table if necessary

        if(!pte_parent || !pte_child)
          panic("fork: walkpgdir failed");

        if(*pte_parent & PTE_P){
          uint pa = PTE_ADDR(*pte_parent);
          uint flags = PTE_FLAGS(*pte_parent);

          // Handle copy-on-write if necessary
          if(flags & PTE_W){
            flags &= ~PTE_W;
            flags |= PTE_COW;
            *pte_parent &= ~PTE_W;
            *pte_parent |= PTE_COW;
          }

          *pte_child = pa | flags;

          // Increment reference count for the physical page
          inc_ref_count_locked(P2V(pa));
        }
      }
    }
  }

  // Adjust parent's PTEs to be read-only and set PTE_COW where appropriate
  mark_parent_pages_cow(curproc->pgdir, curproc->sz);

  // Flush TLB for parent and child
  lcr3(V2P(curproc->pgdir)); // Parent
  lcr3(V2P(np->pgdir));      // Child

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  // Unmap all memory mappings
  for(int i = 0; i < MAX_WMMAP_INFO; i++){
    if(curproc->maps[i].valid){
      uint addr = curproc->maps[i].addr;
      uint length = curproc->maps[i].length;
      uint a = PGROUNDDOWN(addr);
      uint last = PGROUNDDOWN(addr + length - 1);

      for(; a <= last; a += PGSIZE){
        pte_t *pte = walkpgdir(curproc->pgdir, (char*)a, 0);
        if(pte && (*pte & PTE_P)){
          uint pa = PTE_ADDR(*pte);

          // Decrement reference count and free if necessary
          dec_ref_count_locked(P2V(pa));
          if(get_ref_count_locked(P2V(pa)) == 0){
            kfree(P2V(pa));
          }

          // Clear the PTE
          *pte = 0;
        }
      }

      // Mark the mapping as invalid
      curproc->maps[i].valid = 0;
    }
  }

  // Flush the TLB
  lcr3(V2P(curproc->pgdir));

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}


// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

uint
wmap(uint addr, int length, int flags, int fd)
{
  struct proc *curproc = myproc();
  struct file *f = 0;
  
  // Validate arguments
  if(length <= 0)
    return FAILED;

  // Check required flags
  if((flags & MAP_FIXED) == 0 || (flags & MAP_SHARED) == 0)
    return FAILED;

  // Validate address range
  if(addr < 0x60000000 || addr + length > 0x80000000 || addr % PGSIZE != 0)
    return FAILED;

  // For file-backed mapping
  if(!(flags & MAP_ANONYMOUS)) {
    if(fd < 0 || fd >= NOFILE || (f = curproc->ofile[fd]) == 0)
      return FAILED;
    // Verify it's an inode and opened with RDWR
    if(f->type != FD_INODE || !(f->writable && f->readable))
      return FAILED;
    filedup(f);  // Increment ref count
  }

  // Find free mapping slot
  int i;
  for(i = 0; i < MAX_WMMAP_INFO; i++) {
    if(!curproc->maps[i].valid)
      break;
  }
  if(i == MAX_WMMAP_INFO)
    return FAILED;

  // Initialize mapping
  curproc->maps[i].addr = addr;
  curproc->maps[i].length = length;
  curproc->maps[i].flags = flags;
  curproc->maps[i].valid = 1;
  curproc->maps[i].n_loaded_pages = 0;
  curproc->maps[i].f = f;

  return addr;
}

int
wunmap(uint addr)
{
  struct proc *curproc = myproc();
  pde_t *pgdir = curproc->pgdir;

  // Check if address is page-aligned
  if(addr % PGSIZE != 0)
    return FAILED;

  // Find the mapping
  int map_index = -1;
  for(int i = 0; i < MAX_WMMAP_INFO; i++) {
    if(curproc->maps[i].valid && curproc->maps[i].addr == addr) {
      map_index = i;
      break;
    }
  }

  // Return error if no mapping found at this address
  if(map_index == -1)
    return FAILED;

  struct mapping *m = &curproc->maps[map_index];
  uint num_pages = (m->length + PGSIZE - 1) / PGSIZE;

  // For each page in the mapping
  for(uint offset = 0; offset < num_pages * PGSIZE; offset += PGSIZE) {
    uint va = addr + offset;
    pte_t *pte = walkpgdir(pgdir, (char*)va, 0);

    // Skip if page wasn't allocated (due to lazy allocation)
    if(!pte || !(*pte & PTE_P))
      continue;

    // Get the physical address
    uint pa = PTE_ADDR(*pte);

    // If this is a file-backed MAP_SHARED mapping, write back to file
    if(m->f && (m->flags & MAP_SHARED)) {
      // Calculate file offset for this page
      uint file_offset = offset;

      // If this offset is within file bounds
      if(file_offset < m->length) {
        struct file *f = m->f;

        // Write the page contents back to file
        ilock(f->ip);
        // Only write up to the remaining length for the last page
        uint write_size = PGSIZE;
        if(file_offset + PGSIZE > m->length)
          write_size = m->length - file_offset;

        writei(f->ip, P2V(pa), file_offset, write_size);
        iunlock(f->ip);
      }
    }

    // Free the physical page
    kfree(P2V(pa));

    // Clear the PTE
    *pte = 0;
  }

  // If it was a file mapping, close the file
  if(m->f) {
    fileclose(m->f);
    m->f = 0;
  }

  // Mark the mapping as invalid
  m->valid = 0;

  // Flush the TLB
  lcr3(V2P(pgdir));

  return SUCCESS;
}

uint
va2pa(uint va)
{
  pte_t *pte;
  uint pa;
  struct proc *p = myproc();

  // Walk the page table to find the PTE for the given virtual address
  pte = walkpgdir(p->pgdir, (void*)va, 0);
  if(!pte)
    return -1;  // Invalid virtual address

  if(!(*pte & PTE_P))
    return -1;  // Page not present

  pa = PTE_ADDR(*pte);       // Get the physical page frame address
  pa |= va & 0xFFF;          // Add the offset within the page

  return pa;
}

int
getwmapinfo(struct wmapinfo *wminfo)
{
  struct proc *p = myproc();
  int count = 0;

  if(wminfo == 0)
    return FAILED;

  // Initialize wminfo
  wminfo->total_mmaps = 0;
  for(int i = 0; i < MAX_WMMAP_INFO; i++){
    wminfo->addr[i] = 0;
    wminfo->length[i] = 0;
    wminfo->n_loaded_pages[i] = 0;
  }

  acquire(&ptable.lock);

  for(int i = 0; i < MAX_WMMAP_INFO; i++){
    if(p->maps[i].valid){
      if(count >= MAX_WMMAP_INFO)
        break;

      wminfo->addr[count] = p->maps[i].addr;
      wminfo->length[count] = p->maps[i].length;
      wminfo->n_loaded_pages[count] = p->maps[i].n_loaded_pages;

      count++;
    }
  }

  release(&ptable.lock);

  wminfo->total_mmaps = count;

  return SUCCESS;
}