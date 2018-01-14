/* { dg-do compile { target { *-*-linux* && { ! x32 } } } } */
/* { dg-options "-O2 -mfunction-return=keep -mindirect-branch=thunk -fcheck-pointer-bounds -mmpx -fpic -fno-plt" } */

void bar (char *);
char buf[10];

void
foo (void)
{
  bar (buf);
}

/* { dg-final { scan-assembler "push(?:l|q)\[ \t\]*bar@GOT" } } */
/* { dg-final { scan-assembler "bnd jmp\[ \t\]*__x86_indirect_thunk_bnd" } } */
/* { dg-final { scan-assembler "jmp\[ \t\]*\.LIND" } } */
/* { dg-final { scan-assembler "bnd call\[ \t\]*\.LIND" } } */
/* { dg-final { scan-assembler "bnd ret" } } */
/* { dg-final { scan-assembler {\tpause} } } */
/* { dg-final { scan-assembler {\tlfence} } } */
