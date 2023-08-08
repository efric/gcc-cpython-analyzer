/* -fanalyzer plugin for CPython extension modules  */
/* { dg-options "-g" } */

#define INCLUDE_MEMORY
#include "gcc-plugin.h"
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tree.h"
#include "function.h"
#include "basic-block.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "diagnostic-core.h"
#include "graphviz.h"
#include "options.h"
#include "cgraph.h"
#include "tree-dfa.h"
#include "stringpool.h"
#include "convert.h"
#include "target.h"
#include "fold-const.h"
#include "tree-pretty-print.h"
#include "diagnostic-color.h"
#include "diagnostic-metadata.h"
#include "tristate.h"
#include "bitmap.h"
#include "selftest.h"
#include "function.h"
#include "json.h"
#include "analyzer/analyzer.h"
#include "analyzer/analyzer-language.h"
#include "analyzer/analyzer-logging.h"
#include "ordered-hash-map.h"
#include "options.h"
#include "cgraph.h"
#include "cfg.h"
#include "digraph.h"
#include "analyzer/supergraph.h"
#include "sbitmap.h"
#include "analyzer/call-string.h"
#include "analyzer/program-point.h"
#include "analyzer/store.h"
#include "analyzer/region-model.h"
#include "analyzer/call-details.h"
#include "analyzer/call-info.h"
#include "make-unique.h"

int plugin_is_GPL_compatible;

#if ENABLE_ANALYZER
static GTY (()) hash_map<tree, tree> *analyzer_stashed_types;
static GTY (()) hash_map<tree, tree> *analyzer_stashed_globals;

namespace ana
{
static tree pyobj_record = NULL_TREE;
static tree pyobj_ptr_tree = NULL_TREE;
static tree pyobj_ptr_ptr = NULL_TREE;
static tree varobj_record = NULL_TREE;
static tree pylistobj_record = NULL_TREE;
static tree pylongobj_record = NULL_TREE;
static tree pylongtype_vardecl = NULL_TREE;
static tree pylisttype_vardecl = NULL_TREE;

static tree
get_field_by_name (tree type, const char *name)
{
  for (tree field = TYPE_FIELDS (type); field; field = TREE_CHAIN (field))
    {
      if (TREE_CODE (field) == FIELD_DECL)
        {
          const char *field_name = IDENTIFIER_POINTER (DECL_NAME (field));
          if (strcmp (field_name, name) == 0)
            return field;
        }
    }
  return NULL_TREE;
}

static const svalue *
get_sizeof_pyobjptr (region_model_manager *mgr)
{
  tree size_tree = TYPE_SIZE_UNIT (pyobj_ptr_tree);
  const svalue *sizeof_sval = mgr->get_or_create_constant_svalue (size_tree);
  return sizeof_sval;
}

static bool
arg_is_long_p (const call_details &cd, unsigned idx)
{
  return types_compatible_p (cd.get_arg_type (idx), long_integer_type_node);
}

class kf_PyList_Append : public known_function
{
public:
  bool
  matches_call_types_p (const call_details &cd) const final override
  {
    return (cd.num_args () == 2); // TODO: more checks here
  }
  void impl_call_pre (const call_details &cd) const final override;
  void impl_call_post (const call_details &cd) const final override;
};

void
kf_PyList_Append::impl_call_pre (const call_details &cd) const
{
  region_model_manager *mgr = cd.get_manager ();
  region_model *model = cd.get_model ();

  const svalue *pylist_sval = cd.get_arg_svalue (0);
  const region *pylist_reg
      = model->deref_rvalue (pylist_sval, cd.get_arg_tree (0), cd.get_ctxt ());

  const svalue *newitem_sval = cd.get_arg_svalue (1);
  const region *newitem_reg
      = model->deref_rvalue (pylist_sval, cd.get_arg_tree (0), cd.get_ctxt ());

  // Skip checks if unknown etc
  if (pylist_sval->get_kind () != SK_REGION
      && pylist_sval->get_kind () != SK_CONSTANT)
    return;

  // PyList_Check
  tree ob_type_field = get_field_by_name (pyobj_record, "ob_type");
  const region *ob_type_region
      = mgr->get_field_region (pylist_reg, ob_type_field);
  const svalue *stored_sval
      = model->get_store_value (ob_type_region, cd.get_ctxt ());
  const region *pylist_type_region
      = mgr->get_region_for_global (pylisttype_vardecl);
  tree pylisttype_vardecl_ptr
      = build_pointer_type (TREE_TYPE (pylisttype_vardecl));
  const svalue *pylist_type_ptr
      = mgr->get_ptr_svalue (pylisttype_vardecl_ptr, pylist_type_region);

  if (stored_sval != pylist_type_ptr)
    {
      // TODO: emit diagnostic -Wanalyzer-type-error
      cd.get_ctxt ()->terminate_path ();
      return;
    }

  // Check that new_item is not null
  {
    const svalue *null_ptr
        = mgr->get_or_create_int_cst (newitem_sval->get_type (), 0);
    if (!model->add_constraint (newitem_sval, NE_EXPR, null_ptr,
                                cd.get_ctxt ()))
      {
        // TODO: emit diagnostic here
        cd.get_ctxt ()->terminate_path ();
        return;
      }
  }
}

void
kf_PyList_Append::impl_call_post (const call_details &cd) const
{
  /* Three custom subclasses of custom_edge_info, for handling the various
     outcomes of "realloc".  */

  /* Concrete custom_edge_info: a realloc call that fails, returning NULL.
   */
  class append_realloc_failure : public failed_call_info
  {
  public:
    append_realloc_failure (const call_details &cd) : failed_call_info (cd) {}

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();

      const svalue *pylist_sval = cd.get_arg_svalue (0);
      const region *pylist_reg = model->deref_rvalue (
          pylist_sval, cd.get_arg_tree (0), cd.get_ctxt ());

      /* Identify ob_item field and set it to NULL. */
      tree ob_item_field = get_field_by_name (pylistobj_record, "ob_item");
      const region *ob_item_reg
          = mgr->get_field_region (pylist_reg, ob_item_field);
      const svalue *old_ptr_sval
          = model->get_store_value (ob_item_reg, cd.get_ctxt ());

      if (const region_svalue *old_reg
          = old_ptr_sval->dyn_cast_region_svalue ())
        {
          const region *freed_reg = old_reg->get_pointee ();
          model->unbind_region_and_descendents (freed_reg, POISON_KIND_FREED);
          model->unset_dynamic_extents (freed_reg);
        }

      const svalue *null_sval = mgr->get_or_create_null_ptr (pyobj_ptr_ptr);
      model->set_value (ob_item_reg, null_sval, cd.get_ctxt ());

      if (cd.get_lhs_type ())
        {
          const svalue *neg_one
              = mgr->get_or_create_int_cst (cd.get_lhs_type (), -1);
          model->set_value (cd.get_lhs_region (), neg_one, cd.get_ctxt ());
        }
      return true;
    }
  };

  class realloc_success_no_move : public call_info
  {
  public:
    realloc_success_no_move (const call_details &cd) : call_info (cd) {}

    label_text
    get_desc (bool can_colorize) const final override
    {
      return make_label_text (
          can_colorize, "when %qE succeeds, without moving underlying buffer",
          get_fndecl ());
    }

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();

      const svalue *pylist_sval = cd.get_arg_svalue (0);
      const region *pylist_reg = model->deref_rvalue (
          pylist_sval, cd.get_arg_tree (0), cd.get_ctxt ());

      const svalue *newitem_sval = cd.get_arg_svalue (1);
      const region *newitem_reg = model->deref_rvalue (
          newitem_sval, cd.get_arg_tree (1), cd.get_ctxt ());

      tree ob_size_field = get_field_by_name (varobj_record, "ob_size");
      const region *ob_size_region
          = mgr->get_field_region (pylist_reg, ob_size_field);
      const svalue *ob_size_sval
          = model->get_store_value (ob_size_region, cd.get_ctxt ());
      const svalue *one_sval
          = mgr->get_or_create_int_cst (integer_type_node, 1);
      const svalue *new_size_sval = mgr->get_or_create_binop (
          integer_type_node, PLUS_EXPR, ob_size_sval, one_sval);

      const svalue *sizeof_sval = mgr->get_or_create_cast (
          ob_size_sval->get_type (), get_sizeof_pyobjptr (mgr));
      const svalue *num_allocated_bytes = mgr->get_or_create_binop (
          size_type_node, MULT_EXPR, sizeof_sval, new_size_sval);

      tree ob_item_field = get_field_by_name (pylistobj_record, "ob_item");
      const region *ob_item_region
          = mgr->get_field_region (pylist_reg, ob_item_field);
      const svalue *ob_item_ptr_sval
          = model->get_store_value (ob_item_region, cd.get_ctxt ());

      /* We can only grow in place with a non-NULL pointer and no unknown
       */
      {
        const svalue *null_ptr = mgr->get_or_create_null_ptr (pyobj_ptr_ptr);
        if (!model->add_constraint (ob_item_ptr_sval, NE_EXPR, null_ptr,
                                    cd.get_ctxt ()))
          {
            return false;
          }
      }

      const unmergeable_svalue *underlying_svalue
          = ob_item_ptr_sval->dyn_cast_unmergeable_svalue ();
      const svalue *target_svalue = nullptr;
      const region_svalue *target_region_svalue = nullptr;

      if (underlying_svalue)
        {
          target_svalue = underlying_svalue->get_arg ();
          if (target_svalue->get_kind () != SK_REGION)
            {
              return false;
            }
        }
      else
        {
          if (ob_item_ptr_sval->get_kind () != SK_REGION)
            {
              return false;
            }
          target_svalue = ob_item_ptr_sval;
        }

      target_region_svalue = target_svalue->dyn_cast_region_svalue ();
      const region *curr_reg = target_region_svalue->get_pointee ();

      if (compat_types_p (num_allocated_bytes->get_type (), size_type_node))
        model->set_dynamic_extents (curr_reg, num_allocated_bytes, ctxt);

      model->set_value (ob_size_region, new_size_sval, ctxt);

      const svalue *offset_sval = mgr->get_or_create_binop (
          size_type_node, MULT_EXPR, sizeof_sval, ob_size_sval);
      const region *element_region
          = mgr->get_offset_region (curr_reg, pyobj_ptr_ptr, offset_sval);
      model->set_value (element_region, newitem_sval, cd.get_ctxt ());

      tree ob_refcnt_tree = get_field_by_name (pyobj_record, "ob_refcnt");
      const region *ob_refcnt_region
          = mgr->get_field_region (newitem_reg, ob_refcnt_tree);
      const svalue *curr_refcnt
          = model->get_store_value (ob_refcnt_region, cd.get_ctxt ());
      const svalue *refcnt_one_sval
          = mgr->get_or_create_int_cst (size_type_node, 1);
      const svalue *new_refcnt_sval = mgr->get_or_create_binop (
          size_type_node, PLUS_EXPR, curr_refcnt, refcnt_one_sval);
      model->set_value (ob_refcnt_region, new_refcnt_sval, cd.get_ctxt ());

      if (cd.get_lhs_type ())
        {
          const svalue *zero
              = mgr->get_or_create_int_cst (cd.get_lhs_type (), 0);
          model->set_value (cd.get_lhs_region (), zero, cd.get_ctxt ());
        }
      return true;
    }
  };

  class realloc_success_move : public call_info
  {
  public:
    realloc_success_move (const call_details &cd) : call_info (cd) {}

    label_text
    get_desc (bool can_colorize) const final override
    {
      return make_label_text (can_colorize, "when %qE succeeds, moving buffer",
                              get_fndecl ());
    }

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();
      const svalue *pylist_sval = cd.get_arg_svalue (0);
      const region *pylist_reg = model->deref_rvalue (
          pylist_sval, cd.get_arg_tree (0), cd.get_ctxt ());

      const svalue *newitem_sval = cd.get_arg_svalue (1);
      const region *newitem_reg = model->deref_rvalue (
          newitem_sval, cd.get_arg_tree (1), cd.get_ctxt ());

      tree ob_size_field = get_field_by_name (varobj_record, "ob_size");
      const region *ob_size_region
          = mgr->get_field_region (pylist_reg, ob_size_field);
      const svalue *old_ob_size_sval
          = model->get_store_value (ob_size_region, cd.get_ctxt ());
      const svalue *one_sval
          = mgr->get_or_create_int_cst (integer_type_node, 1);
      const svalue *new_ob_size_sval = mgr->get_or_create_binop (
          integer_type_node, PLUS_EXPR, old_ob_size_sval, one_sval);

      const svalue *sizeof_sval = mgr->get_or_create_cast (
          old_ob_size_sval->get_type (), get_sizeof_pyobjptr (mgr));
      const svalue *new_size_sval = mgr->get_or_create_binop (
          size_type_node, MULT_EXPR, sizeof_sval, new_ob_size_sval);

      tree ob_item_field = get_field_by_name (pylistobj_record, "ob_item");
      const region *ob_item_reg
          = mgr->get_field_region (pylist_reg, ob_item_field);
      const svalue *old_ptr_sval
          = model->get_store_value (ob_item_reg, cd.get_ctxt ());

      /* Create the new region.  */
      const region *new_reg = model->get_or_create_region_for_heap_alloc (
          new_size_sval, cd.get_ctxt ());
      const svalue *new_ptr_sval
          = mgr->get_ptr_svalue (pyobj_ptr_ptr, new_reg);
      if (!model->add_constraint (new_ptr_sval, NE_EXPR, old_ptr_sval,
                                  cd.get_ctxt ()))
        return false;

      if (const region_svalue *old_reg
          = old_ptr_sval->dyn_cast_region_svalue ())
        {
          const region *freed_reg = old_reg->get_pointee ();
          const svalue *old_size_sval = model->get_dynamic_extents (freed_reg);
          if (old_size_sval)
            {
              const svalue *copied_size_sval
                  = get_copied_size (model, old_size_sval, new_size_sval);
              const region *copied_old_reg = mgr->get_sized_region (
                  freed_reg, pyobj_ptr_ptr, copied_size_sval);
              const svalue *buffer_content_sval
                  = model->get_store_value (copied_old_reg, cd.get_ctxt ());
              const region *copied_new_reg = mgr->get_sized_region (
                  new_reg, pyobj_ptr_ptr, copied_size_sval);
              model->set_value (copied_new_reg, buffer_content_sval,
                                cd.get_ctxt ());
            }
          else
            {
              model->mark_region_as_unknown (freed_reg, cd.get_uncertainty ());
            }

          model->unbind_region_and_descendents (freed_reg, POISON_KIND_FREED);
          model->unset_dynamic_extents (freed_reg);
        }

      const svalue *null_ptr = mgr->get_or_create_null_ptr (pyobj_ptr_ptr);
      if (!model->add_constraint (new_ptr_sval, NE_EXPR, null_ptr,
                                  cd.get_ctxt ()))
        return false;

      model->set_value (ob_size_region, new_ob_size_sval, ctxt);
      model->set_value (ob_item_reg, new_ptr_sval, cd.get_ctxt ());

      const svalue *offset_sval = mgr->get_or_create_binop (
          size_type_node, MULT_EXPR, sizeof_sval, old_ob_size_sval);
      const region *element_region
          = mgr->get_offset_region (new_reg, pyobj_ptr_ptr, offset_sval);
      model->set_value (element_region, newitem_sval, cd.get_ctxt ());

      tree ob_refcnt_tree = get_field_by_name (pyobj_record, "ob_refcnt");
      const region *ob_refcnt_region
          = mgr->get_field_region (newitem_reg, ob_refcnt_tree);
      const svalue *curr_refcnt
          = model->get_store_value (ob_refcnt_region, cd.get_ctxt ());
      const svalue *refcnt_one_sval
          = mgr->get_or_create_int_cst (size_type_node, 1);
      const svalue *new_refcnt_sval = mgr->get_or_create_binop (
          size_type_node, PLUS_EXPR, curr_refcnt, refcnt_one_sval);
      model->set_value (ob_refcnt_region, new_refcnt_sval, cd.get_ctxt ());

      if (cd.get_lhs_type ())
        {
          const svalue *zero
              = mgr->get_or_create_int_cst (cd.get_lhs_type (), 0);
          model->set_value (cd.get_lhs_region (), zero, cd.get_ctxt ());
        }
      return true;
    }

  private:
    /* Return the lesser of OLD_SIZE_SVAL and NEW_SIZE_SVAL.
       If unknown, OLD_SIZE_SVAL is returned.  */
    const svalue *
    get_copied_size (region_model *model, const svalue *old_size_sval,
                     const svalue *new_size_sval) const
    {
      tristate res
          = model->eval_condition (old_size_sval, GT_EXPR, new_size_sval);
      switch (res.get_value ())
        {
        case tristate::TS_TRUE:
          return new_size_sval;
        case tristate::TS_FALSE:
        case tristate::TS_UNKNOWN:
          return old_size_sval;
        default:
          gcc_unreachable ();
        }
    }
  };

  /* Body of kf_PyList_Append::impl_call_post.  */
  if (cd.get_ctxt ())
    {
      cd.get_ctxt ()->bifurcate (make_unique<append_realloc_failure> (cd));
      cd.get_ctxt ()->bifurcate (make_unique<realloc_success_no_move> (cd));
      cd.get_ctxt ()->bifurcate (make_unique<realloc_success_move> (cd));
      cd.get_ctxt ()->terminate_path ();
    }
}

class kf_PyList_New : public known_function
{
public:
  bool
  matches_call_types_p (const call_details &cd) const final override
  {
    return (cd.num_args () == 1 && arg_is_long_p (cd, 0));
  }
  void impl_call_post (const call_details &cd) const final override;
};

void
kf_PyList_New::impl_call_post (const call_details &cd) const
{
  class failure : public failed_call_info
  {
  public:
    failure (const call_details &cd) : failed_call_info (cd) {}

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      /* Return NULL; everything else is unchanged.  */
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();
      if (cd.get_lhs_type ())
        {
          const svalue *zero
              = mgr->get_or_create_int_cst (cd.get_lhs_type (), 0);
          model->set_value (cd.get_lhs_region (), zero, cd.get_ctxt ());
        }
      return true;
    }
  };

  class success : public call_info
  {
  public:
    success (const call_details &cd) : call_info (cd) {}

    label_text
    get_desc (bool can_colorize) const final override
    {
      return make_label_text (can_colorize, "when %qE succeeds",
                              get_fndecl ());
    }

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();

      const svalue *pyobj_svalue
          = mgr->get_or_create_unknown_svalue (pyobj_record);
      const svalue *varobj_svalue
          = mgr->get_or_create_unknown_svalue (varobj_record);
      const svalue *pylist_svalue
          = mgr->get_or_create_unknown_svalue (pylistobj_record);

      const svalue *size_sval = cd.get_arg_svalue (0);

      const svalue *tp_basicsize_sval
          = mgr->get_or_create_unknown_svalue (NULL);
      const region *pylist_region
          = model->get_or_create_region_for_heap_alloc (
              tp_basicsize_sval, cd.get_ctxt (), true, &cd);
      model->set_value (pylist_region, pylist_svalue, cd.get_ctxt ());

      /*
      typedef struct
      {
        PyObject_VAR_HEAD
        PyObject **ob_item;
        Py_ssize_t allocated;
      } PyListObject;
      */
      tree varobj_field = get_field_by_name (pylistobj_record, "ob_base");
      const region *varobj_region
          = mgr->get_field_region (pylist_region, varobj_field);
      model->set_value (varobj_region, varobj_svalue, cd.get_ctxt ());

      tree ob_item_field = get_field_by_name (pylistobj_record, "ob_item");
      const region *ob_item_region
          = mgr->get_field_region (pylist_region, ob_item_field);

      const svalue *zero_sval = mgr->get_or_create_int_cst (size_type_node, 0);
      const svalue *casted_size_sval
          = mgr->get_or_create_cast (size_type_node, size_sval);
      const svalue *size_cond_sval = mgr->get_or_create_binop (
          size_type_node, LE_EXPR, casted_size_sval, zero_sval);

      // if size <= 0, ob_item = NULL

      if (tree_int_cst_equal (size_cond_sval->maybe_get_constant (),
                              integer_one_node))
        {
          const svalue *null_sval
              = mgr->get_or_create_null_ptr (pyobj_ptr_ptr);
          model->set_value (ob_item_region, null_sval, cd.get_ctxt ());
        }
      else // calloc
        {
          const svalue *sizeof_sval = mgr->get_or_create_cast (
              size_sval->get_type (), get_sizeof_pyobjptr (mgr));
          const svalue *prod_sval = mgr->get_or_create_binop (
              size_type_node, MULT_EXPR, sizeof_sval, size_sval);
          const region *ob_item_sized_region
              = model->get_or_create_region_for_heap_alloc (prod_sval,
                                                            cd.get_ctxt ());
          model->zero_fill_region (ob_item_sized_region);
          const svalue *ob_item_ptr_sval
              = mgr->get_ptr_svalue (pyobj_ptr_ptr, ob_item_sized_region);
          const svalue *ob_item_unmergeable
              = mgr->get_or_create_unmergeable (ob_item_ptr_sval);
          model->set_value (ob_item_region, ob_item_unmergeable,
                            cd.get_ctxt ());
        }

      /*
      typedef struct {
      PyObject ob_base;
      Py_ssize_t ob_size; // Number of items in variable part
      } PyVarObject;
      */
      tree ob_base_tree = get_field_by_name (varobj_record, "ob_base");
      const region *ob_base_region
          = mgr->get_field_region (varobj_region, ob_base_tree);
      model->set_value (ob_base_region, pyobj_svalue, cd.get_ctxt ());

      tree ob_size_tree = get_field_by_name (varobj_record, "ob_size");
      const region *ob_size_region
          = mgr->get_field_region (varobj_region, ob_size_tree);
      model->set_value (ob_size_region, size_sval, cd.get_ctxt ());

      /*
      typedef struct _object {
          _PyObject_HEAD_EXTRA
          Py_ssize_t ob_refcnt;
          PyTypeObject *ob_type;
      } PyObject;
      */

      tree ob_refcnt_tree = get_field_by_name (pyobj_record, "ob_refcnt");
      const region *ob_refcnt_region
          = mgr->get_field_region (ob_base_region, ob_refcnt_tree);
      const svalue *refcnt_one_sval
          = mgr->get_or_create_int_cst (size_type_node, 1);
      model->set_value (ob_refcnt_region, refcnt_one_sval, cd.get_ctxt ());

      // get pointer svalue for PyList_Type then assign it to ob_type field.
      const region *pylist_type_region
          = mgr->get_region_for_global (pylisttype_vardecl);
      tree pylisttype_vardecl_ptr
          = build_pointer_type (TREE_TYPE (pylisttype_vardecl));
      const svalue *pylist_type_ptr_sval
          = mgr->get_ptr_svalue (pylisttype_vardecl_ptr, pylist_type_region);
      tree ob_type_field = get_field_by_name (pyobj_record, "ob_type");
      const region *ob_type_region
          = mgr->get_field_region (ob_base_region, ob_type_field);
      model->set_value (ob_type_region, pylist_type_ptr_sval, cd.get_ctxt ());

      if (cd.get_lhs_type ())
        {
          const svalue *ptr_sval
              = mgr->get_ptr_svalue (cd.get_lhs_type (), pylist_region);
          cd.maybe_set_lhs (ptr_sval);
        }
      return true;
    }
  };

  if (cd.get_ctxt ())
    {
      cd.get_ctxt ()->bifurcate (make_unique<failure> (cd));
      cd.get_ctxt ()->bifurcate (make_unique<success> (cd));
      cd.get_ctxt ()->terminate_path ();
    }
}

class kf_PyLong_FromLong : public known_function
{
public:
  bool
  matches_call_types_p (const call_details &cd) const final override
  {
    return (cd.num_args () == 1 && arg_is_long_p (cd, 0));
  }
  void impl_call_post (const call_details &cd) const final override;
};

void
kf_PyLong_FromLong::impl_call_post (const call_details &cd) const
{
  class failure : public failed_call_info
  {
  public:
    failure (const call_details &cd) : failed_call_info (cd) {}

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      /* Return NULL; everything else is unchanged.  */
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();
      if (cd.get_lhs_type ())
        {
          const svalue *zero
              = mgr->get_or_create_int_cst (cd.get_lhs_type (), 0);
          model->set_value (cd.get_lhs_region (), zero, cd.get_ctxt ());
        }
      return true;
    }
  };

  class success : public call_info
  {
  public:
    success (const call_details &cd) : call_info (cd) {}

    label_text
    get_desc (bool can_colorize) const final override
    {
      return make_label_text (can_colorize, "when %qE succeeds",
                              get_fndecl ());
    }

    bool
    update_model (region_model *model, const exploded_edge *,
                  region_model_context *ctxt) const final override
    {
      const call_details cd (get_call_details (model, ctxt));
      region_model_manager *mgr = cd.get_manager ();

      const svalue *pyobj_svalue
          = mgr->get_or_create_unknown_svalue (pyobj_record);
      const svalue *pylongobj_sval
          = mgr->get_or_create_unknown_svalue (pylongobj_record);
      tree pylongtype_vardecl_ptr
          = build_pointer_type (TREE_TYPE (pylongtype_vardecl));

      const svalue *tp_basicsize_sval
          = mgr->get_or_create_unknown_svalue (NULL);
      const region *new_pylong_region
          = model->get_or_create_region_for_heap_alloc (
              tp_basicsize_sval, cd.get_ctxt (), true, &cd);
      model->set_value (new_pylong_region, pylongobj_sval, cd.get_ctxt ());

      // Create a region for the base PyObject within the PyLongObject.
      tree ob_base_tree = get_field_by_name (pylongobj_record, "ob_base");
      const region *ob_base_region
          = mgr->get_field_region (new_pylong_region, ob_base_tree);
      model->set_value (ob_base_region, pyobj_svalue, cd.get_ctxt ());

      tree ob_refcnt_tree = get_field_by_name (pyobj_record, "ob_refcnt");
      const region *ob_refcnt_region
          = mgr->get_field_region (ob_base_region, ob_refcnt_tree);
      const svalue *refcnt_one_sval
          = mgr->get_or_create_int_cst (size_type_node, 1);
      model->set_value (ob_refcnt_region, refcnt_one_sval, cd.get_ctxt ());

      // get pointer svalue for PyLong_Type then assign it to ob_type field.
      const region *pylong_type_region
          = mgr->get_region_for_global (pylongtype_vardecl);
      const svalue *pylong_type_ptr_sval
          = mgr->get_ptr_svalue (pylongtype_vardecl_ptr, pylong_type_region);
      tree ob_type_field = get_field_by_name (pyobj_record, "ob_type");
      const region *ob_type_region
          = mgr->get_field_region (ob_base_region, ob_type_field);
      model->set_value (ob_type_region, pylong_type_ptr_sval, cd.get_ctxt ());

      // Set the PyLongObject value.
      tree ob_digit_field = get_field_by_name (pylongobj_record, "ob_digit");
      const region *ob_digit_region
          = mgr->get_field_region (new_pylong_region, ob_digit_field);
      const svalue *ob_digit_sval = cd.get_arg_svalue (0);
      model->set_value (ob_digit_region, ob_digit_sval, cd.get_ctxt ());

      if (cd.get_lhs_type ())
        {
          const svalue *ptr_sval
              = mgr->get_ptr_svalue (cd.get_lhs_type (), new_pylong_region);
          cd.maybe_set_lhs (ptr_sval);
        }
      return true;
    }
  };

  if (cd.get_ctxt ())
    {
      cd.get_ctxt ()->bifurcate (make_unique<failure> (cd));
      cd.get_ctxt ()->bifurcate (make_unique<success> (cd));
      cd.get_ctxt ()->terminate_path ();
    }
}

static void
maybe_stash_named_type (logger *logger, const translation_unit &tu,
                        const char *name)
{
  LOG_FUNC_1 (logger, "name: %qs", name);
  if (!analyzer_stashed_types)
    analyzer_stashed_types = hash_map<tree, tree>::create_ggc ();

  tree id = get_identifier (name);
  if (tree t = tu.lookup_type_by_id (id))
    {
      gcc_assert (TREE_CODE (t) == RECORD_TYPE);
      analyzer_stashed_types->put (id, t);
      if (logger)
        logger->log ("found %qs: %qE", name, t);
    }
  else
    {
      if (logger)
        logger->log ("%qs: not found", name);
    }
}

static void
maybe_stash_global_var (logger *logger, const translation_unit &tu,
                        const char *name)
{
  LOG_FUNC_1 (logger, "name: %qs", name);
  if (!analyzer_stashed_globals)
    analyzer_stashed_globals = hash_map<tree, tree>::create_ggc ();

  tree id = get_identifier (name);
  if (tree t = tu.lookup_global_var_by_id (id))
    {
      gcc_assert (TREE_CODE (t) == VAR_DECL);
      analyzer_stashed_globals->put (id, t);
      if (logger)
        logger->log ("found %qs: %qE", name, t);
    }
  else
    {
      if (logger)
        logger->log ("%qs: not found", name);
    }
}

static void
stash_named_types (logger *logger, const translation_unit &tu)
{
  LOG_SCOPE (logger);

  maybe_stash_named_type (logger, tu, "PyObject");
  maybe_stash_named_type (logger, tu, "PyListObject");
  maybe_stash_named_type (logger, tu, "PyVarObject");
  maybe_stash_named_type (logger, tu, "PyLongObject");
}

static void
stash_global_vars (logger *logger, const translation_unit &tu)
{
  LOG_SCOPE (logger);

  maybe_stash_global_var (logger, tu, "PyLong_Type");
  maybe_stash_global_var (logger, tu, "PyList_Type");
}

static tree
get_stashed_type_by_name (const char *name)
{
  if (!analyzer_stashed_types)
    return NULL_TREE;
  tree id = get_identifier (name);
  if (tree *slot = analyzer_stashed_types->get (id))
    {
      gcc_assert (TREE_CODE (*slot) == RECORD_TYPE);
      return *slot;
    }
  return NULL_TREE;
}

static tree
get_stashed_global_var_by_name (const char *name)
{
  if (!analyzer_stashed_globals)
    return NULL_TREE;
  tree id = get_identifier (name);
  if (tree *slot = analyzer_stashed_globals->get (id))
    {
      gcc_assert (TREE_CODE (*slot) == VAR_DECL);
      return *slot;
    }
  return NULL_TREE;
}

static void
init_py_structs ()
{
  pyobj_record = get_stashed_type_by_name ("PyObject");
  varobj_record = get_stashed_type_by_name ("PyVarObject");
  pylistobj_record = get_stashed_type_by_name ("PyListObject");
  pylongobj_record = get_stashed_type_by_name ("PyLongObject");
  pylongtype_vardecl = get_stashed_global_var_by_name ("PyLong_Type");
  pylisttype_vardecl = get_stashed_global_var_by_name ("PyList_Type");

  if (pyobj_record)
    {
      pyobj_ptr_tree = build_pointer_type (pyobj_record);
      pyobj_ptr_ptr = build_pointer_type (pyobj_ptr_tree);
    }
}

void
sorry_no_cpython_plugin ()
{
  sorry ("%qs definitions not found."
	 " Please ensure to %qs.)",
	 "Python/C API", "#include <Python.h>");
}

static void
cpython_analyzer_init_cb (void *gcc_data, void * /*user_data */)
{
  ana::plugin_analyzer_init_iface *iface
      = (ana::plugin_analyzer_init_iface *)gcc_data;
  LOG_SCOPE (iface->get_logger ());
  if (0)
    inform (input_location, "got here: cpython_analyzer_init_cb");

  init_py_structs ();

  if (pyobj_record == NULL_TREE)
    {
      sorry_no_cpython_plugin ();
      return;
    }

  iface->register_known_function ("PyLong_FromLong",
                                  make_unique<kf_PyLong_FromLong> ());
  iface->register_known_function ("PyList_New", make_unique<kf_PyList_New> ());
  iface->register_known_function ("PyList_Append",
                                  make_unique<kf_PyList_Append> ());
}
} // namespace ana

#endif /* #if ENABLE_ANALYZER */

int
plugin_init (struct plugin_name_args *plugin_info,
             struct plugin_gcc_version *version)
{
#if ENABLE_ANALYZER
  const char *plugin_name = plugin_info->base_name;
  if (0)
    inform (input_location, "got here; %qs", plugin_name);
  ana::register_finish_translation_unit_callback (&stash_named_types);
  ana::register_finish_translation_unit_callback (&stash_global_vars);
  register_callback (plugin_info->base_name, PLUGIN_ANALYZER_INIT,
                     ana::cpython_analyzer_init_cb,
                     NULL); /* void *user_data */
#else
  sorry_no_analyzer ();
#endif
  return 0;
}