#include "types.h"
#include "x86.h"
#include "defs.h"
#include "date.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

int
sys_fork(void)
{
  return fork();
}

int
sys_exit(void)
{
  exit();
  return 0;  // not reached
}

int
sys_wait(void)
{
  return wait();
}

int
sys_kill(void)
{
  int pid;

  if(argint(0, &pid) < 0)
    return -1;
  return kill(pid);
}

int
sys_getpid(void)
{
  return myproc()->pid;
}

int
sys_sbrk(void)
{
  int addr;
  int n;

  if(argint(0, &n) < 0)
    return -1;
  addr = myproc()->sz;
  if(growproc(n) < 0)
    return -1;
  return addr;
}

int
sys_sleep(void)
{
  int n;
  uint ticks0;

  if(argint(0, &n) < 0)
    return -1;
  acquire(&tickslock);
  ticks0 = ticks;
  while(ticks - ticks0 < n){
    if(myproc()->killed){
      release(&tickslock);
      return -1;
    }
    sleep(&ticks, &tickslock);
  }
  release(&tickslock);
  return 0;
}

// return how many clock tick interrupts have occurred
// since start.
int
sys_uptime(void)
{
  uint xticks;

  acquire(&tickslock);
  xticks = ticks;
  release(&tickslock);
  return xticks;
}


int
sys_wmap(void)
{
  uint addr;
  int length, flags, fd;
  struct file *f;
  
  if(argint(1, &length) < 0 || argint(2, &flags) < 0 || argint(3, &fd) < 0 || argptr(0, (void*)&addr, sizeof(addr)) < 0)
    return FAILED;

  // Validate arguments
  if(length <= 0)
    return FAILED;

  // Check required flags
  if((flags & MAP_FIXED) == 0 || (flags & MAP_SHARED) == 0)
    return FAILED;

  // Validate address range
  if(addr < 0x60000000 || addr + length > 0x80000000 || addr % PGSIZE != 0)
    return FAILED;

  struct proc *curproc = myproc();
  
  // Find free mapping slot
  int i;
  for(i = 0; i < MAX_WMMAP_INFO; i++) {
    if(!curproc->maps[i].valid)
      break;
  }
  if(i == MAX_WMMAP_INFO)
    return FAILED;

  // For file-backed mapping
  if(!(flags & MAP_ANONYMOUS)) {
    if(fd < 0 || fd >= NOFILE || (f = curproc->ofile[fd]) == 0)
      return FAILED;
    // Verify it's an inode and opened with RDWR
    if(f->type != FD_INODE || !(f->writable && f->readable))
      return FAILED;
    curproc->maps[i].f = f;
    filedup(f);  // Increment ref count
  } else {
    curproc->maps[i].f = 0;
  }

  // Initialize mapping
  curproc->maps[i].addr = addr;
  curproc->maps[i].length = length;
  curproc->maps[i].flags = flags;
  curproc->maps[i].valid = 1;
  curproc->maps[i].n_loaded_pages = 0;

  return addr;
}

int
sys_wunmap(void)
{
  uint addr;
  if(argptr(0, (void*)&addr, sizeof(addr)) < 0)
    return FAILED;

  // Check if address is page-aligned
  if(addr % PGSIZE != 0)
    return FAILED;

  struct proc *curproc = myproc();
  pde_t *pgdir = curproc->pgdir;
  
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
  
  // Update TLB
  lcr3(V2P(pgdir));
  
  return SUCCESS;
}

int
sys_va2pa(void)
{
  uint va;
  if(argint(0, (int*)&va) < 0)
    return -1;
  return va2pa(va);
}

int
sys_getwmapinfo(void)
{
  struct wmapinfo *wminfo;
  if(argptr(0, (void*)&wminfo, sizeof(*wminfo)) < 0)
    return FAILED;
  return getwmapinfo(wminfo);
}