/* Interface between analyzer and frontends.
   Copyright (C) 2022-2023 Free Software Foundation, Inc.
   Contributed by David Malcolm <dmalcolm@redhat.com>.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#define INCLUDE_MEMORY
#include "system.h"
#include "coretypes.h"
#include "tree.h"
#include "stringpool.h"
#include "analyzer/analyzer.h"
#include "analyzer/analyzer-language.h"
#include "analyzer/analyzer-logging.h"
#include "diagnostic.h"

/* Map from identifier to INTEGER_CST.  */
static GTY (()) hash_map <tree, tree> *analyzer_stashed_constants;
static GTY (()) hash_map <tree, tree> *analyzer_stashed_types;
static GTY (()) hash_map <tree, tree> *analyzer_stashed_globals;

#if ENABLE_ANALYZER

namespace ana {

/* Call into TU to try to find a value for NAME.
   If found, stash its value within analyzer_stashed_constants.  */

static void
maybe_stash_named_constant (logger *logger,
			    const translation_unit &tu,
			    const char *name)
{
  LOG_FUNC_1 (logger, "name: %qs", name);

  if (!analyzer_stashed_constants)
    analyzer_stashed_constants = hash_map<tree, tree>::create_ggc ();

  tree id = get_identifier (name);
  if (tree t = tu.lookup_constant_by_id (id))
    {
      gcc_assert (TREE_CODE (t) == INTEGER_CST);
      analyzer_stashed_constants->put (id, t);
      if (logger)
	logger->log ("%qs: %qE", name, t);
    }
  else
    {
      if (logger)
	logger->log ("%qs: not found", name);
    }
}

static void
maybe_stash_named_type(logger *logger,
                           const translation_unit &tu,
                           const char *name)
{
    LOG_FUNC_1(logger, "name: %qs", name);
    if (!analyzer_stashed_types)
      analyzer_stashed_types = hash_map<tree, tree>::create_ggc();

    tree id = get_identifier(name);
    if (tree t = tu.lookup_type_by_id(id))
    {
      gcc_assert (TREE_CODE (t) == RECORD_TYPE);
      analyzer_stashed_types->put (id, t);
      if (logger)
      {
  logger->log("found %qs: %qE", name, t);
      }
    }
    else
    {
      if (logger)
  logger->log("%qs: not found", name);
    }
}

static void
maybe_stash_global_var(logger *logger,
                           const translation_unit &tu,
                           const char *name)
{
    LOG_FUNC_1(logger, "name: %qs", name);
    if (!analyzer_stashed_globals)
      analyzer_stashed_globals = hash_map<tree, tree>::create_ggc();

    tree id = get_identifier(name);
    if (tree t = tu.lookup_global_var_by_id(id))
    {
      gcc_assert (TREE_CODE (t) == RECORD_TYPE);
      analyzer_stashed_globals->put (id, t);
      if (logger)
      {
  logger->log("found %qs: %qE", name, t);
      }
    }
    else
    {
      if (logger)
  logger->log("%qs: not found", name);
    }
}

/* Call into TU to try to find values for the names we care about.
   If found, stash their values within analyzer_stashed_constants.  */

static void
stash_named_constants (logger *logger, const translation_unit &tu)
{
  LOG_SCOPE (logger);

  /* Stash named constants for use by sm-fd.cc  */
  maybe_stash_named_constant (logger, tu, "O_ACCMODE");
  maybe_stash_named_constant (logger, tu, "O_RDONLY");
  maybe_stash_named_constant (logger, tu, "O_WRONLY");
  maybe_stash_named_constant (logger, tu, "SOCK_STREAM");
  maybe_stash_named_constant (logger, tu, "SOCK_DGRAM");
}

/* Call into TU to try to find values for the names we care about.
   If found, stash their values within analyzer_stashed_types  */

// suggestion: add some functionality for plugins 
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

/* Hook for frontend to call into analyzer when TU finishes.
   This exists so that the analyzer can stash named constant values from
   header files (e.g. macros and enums) for later use when modeling the
   behaviors of APIs.

   By doing it this way, the analyzer can use the precise values for those
   constants from the user's headers, rather than attempting to model them
   as properties of the target.  */

void
on_finish_translation_unit (const translation_unit &tu)
{
  /* Bail if the analyzer isn't enabled.  */
  if (!flag_analyzer)
    return;

  FILE *logfile = get_or_create_any_logfile ();
  log_user the_logger (NULL);
  if (logfile)
    the_logger.set_logger (new logger (logfile, 0, 0,
				       *global_dc->printer));
  stash_named_constants (the_logger.get_logger (), tu);

  // TODO: perhaps later add to only do this if plugin itself is enabled
  // plugin hook
  stash_named_types (the_logger.get_logger (), tu);
  stash_global_vars (the_logger.get_logger (), tu);
}

/* Lookup NAME in the named constants stashed when the frontend TU finished.
   Return either an INTEGER_CST, or NULL_TREE.  */

tree
get_stashed_constant_by_name (const char *name)
{
  if (!analyzer_stashed_constants)
    return NULL_TREE;
  tree id = get_identifier (name);
  if (tree *slot = analyzer_stashed_constants->get (id))
    {
      gcc_assert (TREE_CODE (*slot) == INTEGER_CST);
      return *slot;
    }
  return NULL_TREE;
}

tree
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

tree
get_stashed_global_var_by_name (const char *name)
{
  if (!analyzer_stashed_globals)
    return NULL_TREE;
  tree id = get_identifier (name);
  if (tree *slot = analyzer_stashed_globals->get (id))
    {
      gcc_assert (TREE_CODE (*slot) == RECORD_TYPE);
      return *slot;
    }
  return NULL_TREE;
}

/* Log all stashed named constants to LOGGER.  */

void
log_stashed_constants (logger *logger)
{
  gcc_assert (logger);
  LOG_SCOPE (logger);
  if (analyzer_stashed_constants)
    for (auto iter : *analyzer_stashed_constants)
      logger->log ("%qE: %qE", iter.first, iter.second);
}

} // namespace ana

#endif /* #if ENABLE_ANALYZER */

#include "gt-analyzer-language.h"
