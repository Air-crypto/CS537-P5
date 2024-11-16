#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "x86.h"
#include "traps.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint vectors[];  // in vectors.S: array of 256 entry pointers
struct spinlock tickslock;
uint ticks;

void
tvinit(void)
{
  int i;

  for(i = 0; i < 256; i++)
    SETGATE(idt[i], 0, SEG_KCODE<<3, vectors[i], 0);
  SETGATE(idt[T_SYSCALL], 1, SEG_KCODE<<3, vectors[T_SYSCALL], DPL_USER);

  initlock(&tickslock, "time");
}

void
idtinit(void)
{
  lidt(idt, sizeof(idt));
}

//PAGEBREAK: 41
void
trap(struct trapframe *tf)
{
  if(tf->trapno == T_SYSCALL){
    if(myproc()->killed)
      exit();
    myproc()->tf = tf;
    syscall();
    if(myproc()->killed)
      exit();
    return;
  }

  switch(tf->trapno){
  case T_IRQ0 + IRQ_TIMER:
    if(cpuid() == 0){
      acquire(&tickslock);
      ticks++;
      wakeup(&ticks);
      release(&tickslock);
    }
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE:
    ideintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE+1:
    // Bochs generates spurious IDE1 interrupts.
    break;
  case T_IRQ0 + IRQ_KBD:
    kbdintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_COM1:
    uartintr();
    lapiceoi();
    break;
  case T_IRQ0 + 7:
  case T_IRQ0 + IRQ_SPURIOUS:
    cprintf("cpu%d: spurious interrupt at %x:%x\n",
            cpuid(), tf->cs, tf->eip);
    lapiceoi();
    break;

  case T_PGFLT: {
    uint va = rcr2();  // Get faulting virtual address
    struct proc *curproc = myproc();

    // First check if it's a COW page fault
    pte_t *pte = walkpgdir(curproc->pgdir, (void*)PGROUNDDOWN(va), 0);
    if(pte && (*pte & PTE_P) && (*pte & PTE_COW)) {
      char *mem;
      uint pa = PTE_ADDR(*pte);
      
      // Allocate new page
      if((mem = kalloc()) == 0) {
        cprintf("cow: out of memory\n");
        curproc->killed = 1;
        return;
      }
      
      // Copy the old page
      memmove(mem, P2V(pa), PGSIZE);
      
      // Map the new page RW
      uint flags = PTE_FLAGS(*pte);
      flags = (flags | PTE_W) & ~PTE_COW;  // Make writable and clear COW flag
      
      if(mappages(curproc->pgdir, (void*)PGROUNDDOWN(va), PGSIZE, V2P(mem), flags) < 0) {
        kfree(mem);
        cprintf("cow: mappages failed\n");
        curproc->killed = 1;
        return;
      }
      
      // Decrement reference count of old page
      dec_ref_count(P2V(pa));
      
      // Flush TLB
      lcr3(V2P(curproc->pgdir));
      
      return;
    }
    
    // Check if address is in any mapping
    for(int i = 0; i < MAX_WMMAP_INFO; i++) {
      if(!curproc->maps[i].valid)
        continue;
        
      uint start = curproc->maps[i].addr;
      uint end = start + curproc->maps[i].length;
      
      if(va >= start && va < end) {
        // Align to page boundary
        va = PGROUNDDOWN(va);
        
        char *mem = kalloc();
        if(mem == 0) {
          cprintf("wmap: out of memory\n");
          myproc()->killed = 1;
          return;
        }
        memset(mem, 0, PGSIZE);
        
        // For file-backed mapping, read from file
        if(curproc->maps[i].f) {
          int offset = va - start;
          struct file *f = curproc->maps[i].f;
          ilock(f->ip);
          readi(f->ip, mem, offset, PGSIZE);
          iunlock(f->ip);
        }
        
        if(mappages(curproc->pgdir, (char*)va, PGSIZE, V2P(mem), PTE_W|PTE_U) < 0) {
          kfree(mem);
          cprintf("wmap: mappages failed\n");
          myproc()->killed = 1;
          return;
        }
        
        curproc->maps[i].n_loaded_pages++;
        return;
      }
  }
  
  cprintf("Segmentation Fault\n");
  myproc()->killed = 1;
  return;
}

  //PAGEBREAK: 13
  default:
    if(myproc() == 0 || (tf->cs&3) == 0){
      // In kernel, it must be our mistake.
      cprintf("unexpected trap %d from cpu %d eip %x (cr2=0x%x)\n",
              tf->trapno, cpuid(), tf->eip, rcr2());
      panic("trap");
    }
    // In user space, assume process misbehaved.
    cprintf("pid %d %s: trap %d err %d on cpu %d "
            "eip 0x%x addr 0x%x--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno,
            tf->err, cpuid(), tf->eip, rcr2());
    myproc()->killed = 1;
  }

  // Force process exit if it has been killed and is in user space.
  // (If it is still executing in the kernel, let it keep running
  // until it gets to the regular system call return.)
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();

  // Force process to give up CPU on clock tick.
  // If interrupts were on while locks held, would need to check nlock.
  if(myproc() && myproc()->state == RUNNING &&
     tf->trapno == T_IRQ0+IRQ_TIMER)
    yield();

  // Check if the process has been killed since we yielded
  if(myproc() && myproc()->killed && (tf->cs&3) == DPL_USER)
    exit();
}
