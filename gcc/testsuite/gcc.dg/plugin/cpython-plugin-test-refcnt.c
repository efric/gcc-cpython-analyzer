/* { dg-do compile } */
/* { dg-require-effective-target analyzer } */
/* { dg-options "-fanalyzer" } */
/* { dg-require-python-h "" } */


#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include "../analyzer/analyzer-decls.h"

PyObject *
test_refcnt_1 (PyObject *obj)
{
  Py_INCREF(obj);
  Py_INCREF(obj);
  return obj;
  /* { dg-warning "expected 'obj' to have reference count" "" { target *-*-* } .-1 } */
}