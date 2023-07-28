/* { dg-do compile } */
/* { dg-options "-fanalyzer -I/usr/include/python3.9" } */
/* { dg-require-effective-target analyzer } */

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include "../analyzer/analyzer-decls.h"

PyObject *
test_PyList_New (Py_ssize_t len)
{
  PyObject *obj = PyList_New (5);
  if (obj)
    {
     __analyzer_eval (obj->ob_refcnt == 1); /* { dg-warning "TRUE" } */
     __analyzer_eval (PyList_CheckExact (obj)); /* { dg-warning "TRUE" } */
    }
  else
    __analyzer_dump_path (); /* { dg-message "path" } */
  return obj;
}
