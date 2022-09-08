
  .globl times
times:
  pushq %rbp
  movq %rsp, %rbp
  subq $0, %rsp
  pushq %rbx
  pushq %r12
  pushq %r13
  pushq %r14


  jmp times_start
label_8:
  movq $0, %rdx
  movq %rdx, %rax
  jmp times_conclusion
label_9:
  movq $1, %rcx
  negq %rcx
  movq %rsi, %rsi
  addq %rcx, %rsi
  leaq times(%rip), %rcx
  movq %rsi, %rdi
  movq %rdx, %rsi
  movq %rcx, %rax
  callq *%rax
  movq %rax, %rcx
  movq %rdx, %rdx
  addq %rcx, %rdx
  movq %rdx, %rax
  jmp times_conclusion
times_start:
  movq %rdi, %rsi
  movq %rsi, %rdx
  cmpq $0, %rsi
  je label_8
  jmp label_9
times_conclusion:

  addq $0, %rsp
  subq $0, %r15
  popq %r14
  popq %r13
  popq %r12
  popq %rbx
  popq %rbp
  retq

  .globl main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $0, %rsp
  pushq %rbx
  pushq %r12
  pushq %r13
  pushq %r14

  movq $16384, %rdi
  movq $16, %rsi
  callq initialize
  movq rootstack_begin(%rip), %r15

  jmp main_start
main_start:
  leaq times(%rip), %rdx
  movq $2, %rdi
  movq $4, %rsi
  movq %rdx, %rax
  callq *%rax
  jmp main_conclusion
main_conclusion:

  movq %rax, %rdi
  callq print_int
  movq $0, %rax

  addq $0, %rsp
  subq $0, %r15
  popq %r14
  popq %r13
  popq %r12
  popq %rbx
  popq %rbp
  retq
