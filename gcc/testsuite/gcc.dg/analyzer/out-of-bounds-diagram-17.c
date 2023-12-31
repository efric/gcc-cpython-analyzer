/* { dg-additional-options "-fdiagnostics-text-art-charset=unicode" } */

#include <string.h>

void test (void)
{
  char buf[10];
  strcpy (buf, "hello");
  strcat (buf, " world!"); /* { dg-warning "stack-based buffer overflow" } */
  /* { dg-message "write of 3 bytes to beyond the end of 'buf'" "" { target *-*-* } .-1 } */
}

/* { dg-begin-multiline-output "" }
                           ┌─────┬─────┬────┬────┬────┐┌─────┬─────┬─────┐
                           │ [0] │ [1] │[2] │[3] │[4] ││ [5] │ [6] │ [7] │
                           ├─────┼─────┼────┼────┼────┤├─────┼─────┼─────┤
                           │ ' ' │ 'w' │'o' │'r' │'l' ││ 'd' │ '!' │ NUL │
                           ├─────┴─────┴────┴────┴────┴┴─────┴─────┴─────┤
                           │      string literal (type: 'char[8]')       │
                           └─────────────────────────────────────────────┘
                              │     │    │    │    │      │     │     │
                              │     │    │    │    │      │     │     │
                              v     v    v    v    v      v     v     v
  ┌─────┬────────────────────────────────────────┬────┐┌─────────────────┐
  │ [0] │                  ...                   │[9] ││                 │
  ├─────┴────────────────────────────────────────┴────┤│after valid range│
  │             'buf' (type: 'char[10]')              ││                 │
  └───────────────────────────────────────────────────┘└─────────────────┘
  ├─────────────────────────┬─────────────────────────┤├────────┬────────┤
                            │                                   │
                  ╭─────────┴────────╮                ╭─────────┴─────────╮
                  │capacity: 10 bytes│                │overflow of 3 bytes│
                  ╰──────────────────╯                ╰───────────────────╯
   { dg-end-multiline-output "" } */
