
      .globl add1
      add1:
        pushq %rbp
        movq %rsp, %rbp
        subq $0, %rsp
        pushq %rbx	
        pushq %r12	
        pushq %r13	
        pushq %r14
        
      jmp add1_start
      add1_start:
  movq %rdi, %rdx
  movq %rdx, %rdx
  addq $1, %rdx
  movq %rdx, %rax
  jmp add1_conclusion
    add1_conclusion:
    
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
  leaq add1(%rip), %rdx
  movq $41, %rdi
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
    