/* -fanalyzer plugin for cpython extension modules  */
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

// TODO**: format in GNU coding standards
namespace ana
{
    static tree pyobj_tree = NULL_TREE;
    static tree varobj_tree = NULL_TREE;
    static tree pylistobj_tree = NULL_TREE;
    static tree pylongobj_tree = NULL_TREE;
    static tree pylongtype_tree = NULL_TREE;
    static tree pylisttype_tree = NULL_TREE;

    // maybe there is one that already exists in region.cc or region_model.cc?
    const svalue *get_type_size_in_bytes(tree type, region_model_manager *mgr)
    {

        tree type_size = TYPE_SIZE_UNIT(type);

        if (type_size != NULL_TREE && TREE_CODE(type_size) == INTEGER_CST)
        {
            //            HOST_WIDE_INT size_in_bytes = tree_to_uhwi(type_size);
            //            size_t size_in_bytes_unsigned = (size_t)size_in_bytes;
            //            inform(input_location, "Size of struct: %lu bytes\n", size_in_bytes);
            const svalue *sz = mgr->get_or_create_constant_svalue(type_size);
            return sz;
        }

        return mgr->get_or_create_unknown_svalue(type_size);
    }

    const svalue *get_sizeof_pyobjptr(region_model_manager *mgr)
    {
        tree pyobj_ptr_tree = build_pointer_type(pyobj_tree);
        tree size_tree = TYPE_SIZE_UNIT(pyobj_ptr_tree);
        const svalue *sizeof_sval = mgr->get_or_create_constant_svalue(size_tree);
        return sizeof_sval;
    }

    class kf_PyList_Append : public known_function
    {
    public:
        bool matches_call_types_p(const call_details &cd) const final override
        {
            return (cd.num_args() == 2); // TODO: more checks here
        }
        void impl_call_pre(const call_details &) const final override;
    };

    void
    kf_PyList_Append::impl_call_pre(const call_details &cd) const
    {
        // TODO: add check that op is pylisttype
        // TODO: check newitem is not null

        // get len
        // get allocated
        
    }

    class kf_PyList_New : public known_function
    {
    public:
        bool matches_call_types_p(const call_details &cd) const final override
        {
            return (cd.num_args() == 1 && cd.arg_is_long_p(0));
        }
        void impl_call_post(const call_details &cd) const final override;
    };

    void
    kf_PyList_New::impl_call_post(const call_details &cd) const
    {
        class failure : public failed_call_info
        {
        public:
            failure(const call_details &cd)
                : failed_call_info(cd)
            {
            }

            bool update_model(region_model *model,
                              const exploded_edge *,
                              region_model_context *ctxt) const final override
            {
                /* Return NULL; everything else is unchanged.  */
                const call_details cd(get_call_details(model, ctxt));
                region_model_manager *mgr = cd.get_manager();
                if (cd.get_lhs_type())
                {
                    const svalue *zero = mgr->get_or_create_int_cst(cd.get_lhs_type(), 0);
                    model->set_value(cd.get_lhs_region(),
                                     zero,
                                     cd.get_ctxt());
                }
                return true;
            }
        };

        class success : public call_info
        {
        public:
            success(const call_details &cd)
                : call_info(cd)
            {
            }

            label_text get_desc(bool can_colorize) const final override
            {
                return make_label_text(can_colorize,
                                       "when %qE succeeds",
                                       get_fndecl());
            }

            bool update_model(region_model *model,
                              const exploded_edge *,
                              region_model_context *ctxt) const final override
            {
                const call_details cd(get_call_details(model, ctxt));
                region_model_manager *mgr = cd.get_manager();

                const svalue *pyobj_svalue = mgr->get_or_create_unknown_svalue(pyobj_tree);
                const svalue *varobj_svalue = mgr->get_or_create_unknown_svalue(varobj_tree);
                const svalue *pylist_svalue = mgr->get_or_create_unknown_svalue(pylistobj_tree);

                const svalue *size_sval = cd.get_arg_svalue(0);

                // create region for pylist
                const region *pylist_region = model->get_or_create_region_for_heap_alloc(NULL, cd.get_ctxt());
                model->set_value(pylist_region, pylist_svalue, cd.get_ctxt());

                //#define PyObject_VAR_HEAD      PyVarObject ob_base;
                tree varobj_field = get_field_by_name(pylistobj_tree, "ob_base");
                const region *varobj_region = mgr->get_field_region(pylist_region, varobj_field);
                model->set_value(varobj_region, varobj_svalue, cd.get_ctxt());

                // PyObject **ob_item;
                tree ob_item_field = get_field_by_name(pylistobj_tree, "ob_item");
                const region *ob_item_region = mgr->get_field_region(pylist_region, ob_item_field);

                const svalue *zero_sval = mgr->get_or_create_int_cst(size_type_node, 0);
                const svalue *casted_size_sval = mgr->get_or_create_cast(size_type_node, size_sval);
                const svalue *size_cond_sval = mgr->get_or_create_binop(size_type_node, LE_EXPR, casted_size_sval, zero_sval);

                // if size <= 0, ob_item = NULL
                // maybe_get_constant might return NULL_TREE which will then not give us right result
                // TODO: add some extra check here

                if (tree_int_cst_equal(size_cond_sval->maybe_get_constant(), integer_one_node)) 
                {
                    tree pyobj_ptr_tree = build_pointer_type(pyobj_tree);
                    tree pyobject_ptr_ptr_tree = build_pointer_type(pyobj_ptr_tree);
                    const svalue *null_sval = mgr->get_or_create_null_ptr(pyobject_ptr_ptr_tree);
                    model->set_value(ob_item_region, null_sval, cd.get_ctxt());
                }
                else
                {
                    const svalue *sizeof_sval = mgr->get_or_create_cast(size_sval->get_type(), get_sizeof_pyobjptr(mgr));
                    const svalue *prod_sval = mgr->get_or_create_binop(size_type_node, MULT_EXPR,
                                                                       sizeof_sval, size_sval);
                    const region *ob_item_sized_region = mgr->get_sized_region(ob_item_region, NULL_TREE, size_sval);
                    model->zero_fill_region(ob_item_sized_region);
                    const svalue *ob_item_ptr_sval = mgr->get_ptr_svalue(TREE_TYPE(ob_item_field), ob_item_sized_region);
                    model->set_value(ob_item_region, ob_item_ptr_sval, cd.get_ctxt());
                }

                /*
                typedef struct {
                PyObject ob_base;
                Py_ssize_t ob_size; // Number of items in variable part 
                } PyVarObject;
                */
                tree ob_base_tree = get_field_by_name(varobj_tree, "ob_base");
                const region *ob_base_region = mgr->get_field_region(varobj_region, ob_base_tree);
                model->set_value(ob_base_region, pyobj_svalue, cd.get_ctxt());
                
                tree ob_size_tree = get_field_by_name(varobj_tree, "ob_size");
                const region *ob_size_region = mgr->get_field_region(varobj_region, ob_size_tree);
                model->set_value(ob_size_region, size_sval, cd.get_ctxt());

                /*
                typedef struct _object {
                    _PyObject_HEAD_EXTRA
                    Py_ssize_t ob_refcnt;
                    PyTypeObject *ob_type;
                } PyObject;
                */

                tree ob_refcnt_tree = get_field_by_name(pyobj_tree, "ob_refcnt");
                const region *ob_refcnt_region = mgr->get_field_region(ob_base_region, ob_refcnt_tree);
                const svalue *refcnt_one_sval = mgr->get_or_create_long_cst(long_integer_type_node, 1); //TODO: switch to Py_ssize_t
                model->set_value(ob_refcnt_region, refcnt_one_sval, cd.get_ctxt());

                tree ob_type_field = get_field_by_name(pyobj_tree, "ob_type");
                const region *ob_type_region = mgr->get_field_region(ob_base_region, ob_type_field);
                const svalue *type_svalue = mgr->get_or_create_unknown_svalue(TREE_TYPE(ob_type_field)); //TODO: switch to actual
                model->set_value(ob_type_region, type_svalue, cd.get_ctxt());

                if (cd.get_lhs_type())
                {
                    const svalue *ptr_sval = mgr->get_ptr_svalue(cd.get_lhs_type(), pylist_region);
                    cd.maybe_set_lhs(ptr_sval);
                }
                return true;
            }
        };

        if (cd.get_ctxt())
        {
            cd.get_ctxt()->bifurcate(make_unique<failure>(cd));
            cd.get_ctxt()->bifurcate(make_unique<success>(cd));
            cd.get_ctxt()->terminate_path();
        }
    }

    class kf_PyLong_FromLong : public known_function
    {
    public:
        bool matches_call_types_p(const call_details &cd) const final override
        {
            return (cd.num_args() == 1 && cd.arg_is_long_p(0));
        }
        void impl_call_post(const call_details &cd) const final override;
    };

    void
    kf_PyLong_FromLong::impl_call_post(const call_details &cd) const
    {
        class failure : public failed_call_info
        {
        public:
            failure(const call_details &cd)
                : failed_call_info(cd)
            {
            }

            bool update_model(region_model *model,
                              const exploded_edge *,
                              region_model_context *ctxt) const final override
            {
                /* Return NULL; everything else is unchanged.  */
                const call_details cd(get_call_details(model, ctxt));
                region_model_manager *mgr = cd.get_manager();
                if (cd.get_lhs_type())
                {
                    const svalue *zero = mgr->get_or_create_int_cst(cd.get_lhs_type(), 0);
                    model->set_value(cd.get_lhs_region(),
                                     zero,
                                     cd.get_ctxt());
                }
                return true;
            }
        };

        class success : public call_info
        {
        public:
            success(const call_details &cd)
                : call_info(cd)
            {
            }

            label_text get_desc(bool can_colorize) const final override
            {
                return make_label_text(can_colorize,
                                       "when %qE succeeds",
                                       get_fndecl());
            }

            bool update_model(region_model *model,
                              const exploded_edge *,
                              region_model_context *ctxt) const final override
            {
                // const call_details cd(get_call_details(model, ctxt));
                // region_model_manager *mgr = cd.get_manager();
                // const svalue *pyobj_svalue = mgr->get_or_create_unknown_svalue(pyobj_tree);

                // const region *new_pyobj_region = model->get_or_create_region_for_heap_alloc(NULL, cd.get_ctxt());
                // model->set_value(new_pyobj_region, pyobj_svalue, cd.get_ctxt());

                // tree ob_refcnt_tree = get_field_by_name(pyobj_tree, "ob_refcnt");
                // const region *ob_refcnt_region = mgr->get_field_region(new_pyobj_region, ob_refcnt_tree);
                // const svalue *refcnt_one_sval = mgr->get_or_create_long_cst(long_integer_type_node, 1);
                // model->set_value(ob_refcnt_region, refcnt_one_sval, cd.get_ctxt());

                // // TODO: this should really be look up global var by name and set it to pointer of that
                // // so keep that in mind
                // tree ob_type_field = get_field_by_name(pyobj_tree, "ob_type");
                // const region *ob_type_region = mgr->get_field_region(new_pyobj_region, ob_type_field);
                // const svalue *type_svalue = mgr->get_or_create_unknown_svalue(ob_type_field);
                // model->set_value(ob_type_region, type_svalue, cd.get_ctxt());

                // if (cd.get_lhs_type())
                // {
                //     const svalue *ptr_sval = mgr->get_ptr_svalue(cd.get_lhs_type(), new_pyobj_region);
                //     cd.maybe_set_lhs(ptr_sval);
                // }
                // return true;



                const call_details cd(get_call_details(model, ctxt));
                region_model_manager *mgr = cd.get_manager();

                const svalue *pyobj_svalue = mgr->get_or_create_unknown_svalue(pyobj_tree);
                const svalue *pylong_svalue = mgr->get_or_create_unknown_svalue(pylongobj_tree);

                // Create a new region for PyLongObject.
                const region *new_pylong_region = model->get_or_create_region_for_heap_alloc(NULL, cd.get_ctxt());
                model->set_value(new_pylong_region, pylong_svalue, cd.get_ctxt());

                // Create a region for the base PyObject within the PyLongObject.
                tree ob_base_tree = get_field_by_name(pylongobj_tree, "ob_base");
                const region *ob_base_region = mgr->get_field_region(new_pylong_region, ob_base_tree);
                model->set_value(ob_base_region, pyobj_svalue, cd.get_ctxt());

                tree ob_refcnt_tree = get_field_by_name(pyobj_tree, "ob_refcnt");
                const region *ob_refcnt_region = mgr->get_field_region(ob_base_region, ob_refcnt_tree);
                // after u do stash global variabvles, change this to pyssize
                const svalue *refcnt_one_sval = mgr->get_or_create_long_cst(long_integer_type_node, 1);
                model->set_value(ob_refcnt_region, refcnt_one_sval, cd.get_ctxt());

                tree ob_type_field = get_field_by_name(pyobj_tree, "ob_type");
                const region *ob_type_region = mgr->get_field_region(ob_base_region, ob_type_field);
                const svalue *type_svalue = mgr->get_or_create_unknown_svalue(TREE_TYPE(ob_type_field));
                model->set_value(ob_type_region, type_svalue, cd.get_ctxt());

                // Set the PyLongObject value.
                tree ob_digit_field = get_field_by_name(pylongobj_tree, "ob_digit");
                const region *ob_digit_region = mgr->get_field_region(new_pylong_region, ob_digit_field);
                const svalue *ob_digit_sval = cd.get_arg_svalue(0);
                model->set_value(ob_digit_region, ob_digit_sval, cd.get_ctxt());

                if (cd.get_lhs_type())
                {
                    const svalue *ptr_sval = mgr->get_ptr_svalue(cd.get_lhs_type(), new_pylong_region);
                    cd.maybe_set_lhs(ptr_sval);
                }
                return true;
            }
        };

        if (cd.get_ctxt())
        {
            cd.get_ctxt()->bifurcate(make_unique<failure>(cd));
            cd.get_ctxt()->bifurcate(make_unique<success>(cd));
            cd.get_ctxt()->terminate_path();
        }
    }

    class kf_Py_Dealloc : public known_function
    {
    public:
        bool matches_call_types_p(const call_details &cd) const final override
        {
            return (cd.num_args() == 1); // should check that arg is pyobject here
        }
        void impl_call_post(const call_details &) const final override;
    };

    void
    kf_Py_Dealloc::impl_call_post(const call_details &cd) const
    {
        region_model *model = cd.get_model();
        region_model_manager *mgr = cd.get_manager();

        const svalue *pyobj_sval = cd.get_arg_svalue(0);
        const region *pyobj_reg = pyobj_sval->maybe_get_region();

        // check to see if already deallocated
        if (!pyobj_reg)
            return;

        tree ob_refcnt_tree = get_field_by_name(pyobj_tree, "ob_refcnt");
        const region *ob_refcnt_region = mgr->get_field_region(pyobj_reg, ob_refcnt_tree);
        const svalue *ob_refcnt_sval = model->get_store_value(ob_refcnt_region, cd.get_ctxt());

        //        pretty_printer pp, pp1, pp2;
        //        ob_refcnt_sval->dump_to_pp(&pp, true);
        //        inform(input_location, "POST py decref %s\n", pp_formatted_text(&pp));
        //        const svalue *one_sval = mgr->get_or_create_int_cst(integer_type_node, 1);
        //        one_sval->dump_to_pp(&pp1, true);
        //        const svalue *new_ob_refcnt_sval = mgr->get_or_create_binop(integer_type_node, MINUS_EXPR, ob_refcnt_sval, one_sval);
        //        new_ob_refcnt_sval->dump_to_pp(&pp2, true);

        // make sure it's not null
        // use model to check in the future to cmp against 0
        if (tree_int_cst_equal(ob_refcnt_sval->maybe_get_constant(), integer_zero_node))
        {
            model->unbind_region_and_descendents(pyobj_reg, POISON_KIND_FREED);
            model->unset_dynamic_extents(pyobj_reg);
        }
    }

    static void initialize_globals()
    {
        if (pyobj_tree == NULL_TREE)
            pyobj_tree = get_stashed_type_by_name("PyObject");
        if (varobj_tree == NULL_TREE)
            varobj_tree = get_stashed_type_by_name("PyVarObject");
        if (pylistobj_tree == NULL_TREE)
            pylistobj_tree = get_stashed_type_by_name("PyListObject");
        if (pylongobj_tree == NULL_TREE)
            pylongobj_tree = get_stashed_type_by_name("PyLongObject");
        if (pylongtype_tree == NULL_TREE)
            pylongtype_tree = get_stashed_global_var_by_name("PyLong_Type");
        if (pylisttype_tree == NULL_TREE)
            pylisttype_tree = get_stashed_global_var_by_name("PyList_Type");
    }

    static void
    cpython_analyzer_init_cb(void *gcc_data, void * /*user_data*/)
    {
        ana::plugin_analyzer_init_iface *iface = (ana::plugin_analyzer_init_iface *)gcc_data;
        LOG_SCOPE(iface->get_logger());
        if (1)
            inform(input_location, "got here: cpython_analyzer_init_cb");
        
        initialize_globals();
        // if e.g PyObject not found, don't bother registering known functions ***
        if (pyobj_tree == NULL_TREE)
            return;
        iface->register_known_function("PyLong_FromLong",
                                       make_unique<kf_PyLong_FromLong>());
        // PyDECREF is a macro that goes to _Py_DECREF in python 3.9 but Py_DECREF in latest
        // do _Py_Dealloc // check if this works in python 3.11 as well
        iface->register_known_function("_Py_Dealloc",
                                       make_unique<kf_Py_Dealloc>());
        iface->register_known_function("PyList_New",
                                       make_unique<kf_PyList_New>());
    }
} //ana namespace

#endif /* #if ENABLE_ANALYZER */

int plugin_init(struct plugin_name_args *plugin_info,
                struct plugin_gcc_version *version)
{
#if ENABLE_ANALYZER
    const char *plugin_name = plugin_info->base_name;
    if (1)
        inform(input_location, "got here; %qs", plugin_name);
    register_callback(plugin_info->base_name,
                      PLUGIN_ANALYZER_INIT,
                      ana::cpython_analyzer_init_cb,
                      NULL); /* void *user_data */
#else
    sorry_no_analyzer();
#endif
    return 0;
}
