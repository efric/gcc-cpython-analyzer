/* { dg-options "-O2 -fdump-tree-optimized-blocks-details -fdump-ipa-profile-optimized -fdump-ipa-afdo-optimized" } */

struct A {
  A () {}

  virtual int AA (void)
  { return 0; }

};

struct B : public A {
  B () {}

  virtual int AA (void)
  { return 1; }
};

void * __attribute__((noinline,noclone)) wrap (void *p) { return p; }
int
main (void)
{
  A a;
  B b;
  
  A* p;

  int i;

  for (i = 0; i < 10000000; i++)
    {
      p = (A *)wrap ((void *)&a);
      p->AA ();

      p = (B *)wrap ((void *)&b);
      p->AA ();
    }
  
  return 0;
}

/* { dg-final-use-not-autofdo { scan-ipa-dump "Indirect call -> direct call.* AA .will resolve by ipa-profile" "profile" } } */
/* { dg-final-use-autofdo { scan-ipa-dump "Indirect call -> direct call.* AA .will resolve by ipa-profile" "afdo" } } */
/* { dg-final-use-not-autofdo { scan-tree-dump-not "Invalid sum" "optimized" } } */
