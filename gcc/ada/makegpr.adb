------------------------------------------------------------------------------
--                                                                          --
--                         GNAT COMPILER COMPONENTS                         --
--                                                                          --
--                              M A K E G P R                               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2004 Free Software Foundation, Inc.               --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 2,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT;  see file COPYING.  If not, write --
-- to  the Free Software Foundation,  59 Temple Place - Suite 330,  Boston, --
-- MA 02111-1307, USA.                                                      --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line;  use Ada.Command_Line;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Unchecked_Deallocation;

with Csets;
with Gnatvsn;

with GNAT.Directory_Operations; use GNAT.Directory_Operations;
with GNAT.Dynamic_Tables;
with GNAT.Expect;               use GNAT.Expect;
with GNAT.HTable;
with GNAT.OS_Lib;               use GNAT.OS_Lib;
with GNAT.Regpat;               use GNAT.Regpat;

with Makeutl;          use Makeutl;
with MLib.Tgt;         use MLib.Tgt;
with Namet;            use Namet;
with Output;           use Output;
with Opt;              use Opt;
with Osint;            use Osint;
with Prj;              use Prj;
with Prj.Com;          use Prj.Com;
with Prj.Pars;
with Prj.Util;         use Prj.Util;
with Snames;           use Snames;
with System;
with System.Case_Util; use System.Case_Util;
with Table;
with Types;            use Types;

package body Makegpr is

   Max_In_Archives : constant := 50;
   --  The maximum number of arguments for a single invocation of the
   --  Archive Indexer (ar).

   Cpp_Linker : constant String := "c++linker";
   --  The name of a linking script, built one the fly, when there are C++
   --  sources and the C++ compiler is not g++.

   No_Argument : constant Argument_List := (1 .. 0 => null);

   FD : Process_Descriptor;
   --  The process descriptor used when invoking a non GNU compiler with -M
   --  and getting the output with GNAT.Expect.

   Line_Matcher : constant Pattern_Matcher :=
                    Compile ("^.*?\n", Single_Line);
   --  The pattern when using GNAT.Expect for the invocation of a non GNU
   --  compiler with -M.

   Name_Ide              : Name_Id;
   Name_Compiler_Command : Name_Id;
   --  Names of package IDE and its attribute Compiler_Command.
   --  Set up by Initialize.

   Unique_Compile : Boolean := False;
   --  True when switch -u is used on the command line

   type Source_Index_Rec is record
      Id : Other_Source_Id;
      Found : Boolean := False;
   end record;
   --  Used as component of Source_Indexes, to check if an archive need to
   --  be rebuilt.

   type Source_Index_Array is array (Positive range <>) of Source_Index_Rec;
   type Source_Indexes_Ref is access Source_Index_Array;

   procedure Free is new Ada.Unchecked_Deallocation
     (Source_Index_Array, Source_Indexes_Ref);

   Initial_Source_Index_Count : constant Positive := 20;
   Source_Indexes : Source_Indexes_Ref :=
     new Source_Index_Array (1 .. Initial_Source_Index_Count);
   --  A list of the Other_Source_Ids of a project file, with an indication
   --  that they have been found in the archive dependency file.

   Last_Source : Natural := 0;
   --  The index of the last valid component of Source_Indexes

   Compiler_Names : array (Programming_Language) of String_Access;
   --  The names of the compilers to be used. Set up by Get_Compiler.
   --  Used to display the commands spawned.

   Compiler_Paths : array (Programming_Language) of String_Access;
   --  The path names of the compiler to be used. Set up by Get_Compiler.
   --  Used to spawn compiling/linking processes.

   Compiler_Is_Gcc : array (Programming_Language) of Boolean;
   --  An indication that a compiler is a GCC compiler, to be able to use
   --  specific GCC switches.

   Archive_Builder_Path : String_Access := null;
   --  The path name of the archive builder (ar). To be used when spawning
   --  ar commands.

   Archive_Indexer_Path : String_Access := null;
   --  The path name of the archive indexer (ranlib), if it exists.

   Copyright_Output : Boolean := False;
   Usage_Output     : Boolean := False;
   --  Flags to avoid multiple displays of the Copyright notice and of the
   --  Usage.

   Output_File_Name           : String_Access := null;
   --  The name given after a switch -o

   Output_File_Name_Expected  : Boolean := False;
   --  True when last switch was -o

   Project_File_Name          : String_Access := null;
   --  The name of the project file specified with switch -P

   Project_File_Name_Expected : Boolean := False;
   --  True when last switch was -P

   Naming_String   : aliased String := "naming";
   Builder_String  : aliased String := "builder";
   Compiler_String : aliased String := "compiler";
   Binder_String   : aliased String := "binder";
   Linker_String   : aliased String := "linker";
   --  Name of packages to be checked when parsing/processing project files

   List_Of_Packages : aliased String_List :=
     (Naming_String   'Access,
      Builder_String  'Access,
      Compiler_String 'Access,
      Binder_String   'Access,
      Linker_String   'Access);
   Packages_To_Check : constant String_List_Access := List_Of_Packages'Access;
   --  List of the packages to be checked when parsing/processing project
   --  files.

   Main_Project : Project_Id;
   --  The project id of the main project

   type Processor is (None, Linker, Compiler);
   Current_Processor : Processor := None;
   --  This variable changes when switches -*args are used

   Current_Language  : Programming_Language := Lang_Ada;
   --  The compiler language to consider when Processor is Compiler

   package Comp_Opts is new GNAT.Dynamic_Tables
     (Table_Component_Type => String_Access,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 20,
      Table_Increment      => 100);
   Options : array (Programming_Language) of Comp_Opts.Instance;
   --  Tables to store compiling options for the different compilers

   package Linker_Options is new Table.Table
     (Table_Component_Type => String_Access,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 20,
      Table_Increment      => 100,
      Table_Name           => "Makegpr.Linker_Options");
   --  Table to store the linking options

   package Ada_Mains is new Table.Table
     (Table_Component_Type => String_Access,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 20,
      Table_Increment      => 100,
      Table_Name           => "Makegpr.Ada_Mains");
   --  Table to store the Ada mains, either specified on the command line
   --  or found in attribute Main of the main project file.

   package Other_Mains is new Table.Table
     (Table_Component_Type => Other_Source,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 20,
      Table_Increment      => 100,
      Table_Name           => "Makegpr.Other_Mains");
   --  Table to store the mains of languages other than Ada, either specified
   --  on the command line or found in attribute Main of the main project file.

   package Sources_Compiled is new GNAT.HTable.Simple_HTable
     (Header_Num => Header_Num,
      Element    => Boolean,
      No_Element => False,
      Key        => Name_Id,
      Hash       => Hash,
      Equal      => "=");

   Initial_Argument_Count : constant Positive := 20;
   type Boolean_Array is array (Positive range <>) of Boolean;
   type Booleans is access Boolean_Array;

   procedure Free is new Ada.Unchecked_Deallocation (Boolean_Array, Booleans);

   Arguments : Argument_List_Access :=
     new Argument_List (1 .. Initial_Argument_Count);
   --  Used to store lists of arguments to be used when spawning a process

   Arguments_Displayed : Booleans :=
     new Boolean_Array (1 .. Initial_Argument_Count);
   --  For each argument in Arguments, indicate if the argument should be
   --  displayed when procedure Display_Command is called.

   Last_Argument : Natural := 0;
   --  Index of the last valid argument in Arguments

   package Cache_Args is new Table.Table
     (Table_Component_Type => String_Access,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 200,
      Table_Increment      => 50,
      Table_Name           => "Makegpr.Cache_Args");
   --  A table to cache arguments, to avoid multiple allocation of the same
   --  strings. It is not possible to use a hash table, because String is
   --  an unconstrained type.

   --  Various switches used when spawning processes:

   Dash_B_String     : aliased  String := "-B";
   Dash_B            : constant String_Access := Dash_B_String'Access;
   Dash_c_String     : aliased  String := "-c";
   Dash_c            : constant String_Access := Dash_c_String'Access;
   Dash_cargs_String : aliased  String := "-cargs";
   Dash_cargs        : constant String_Access := Dash_cargs_String'Access;
   Dash_f_String     : aliased  String := "-f";
   Dash_f            : constant String_Access := Dash_f_String'Access;
   Dash_k_String     : aliased  String := "-k";
   Dash_k            : constant String_Access := Dash_k_String'Access;
   Dash_largs_String : aliased  String := "-largs";
   Dash_largs        : constant String_Access := Dash_largs_String'Access;
   Dash_M_String     : aliased  String := "-M";
   Dash_M            : constant String_Access := Dash_M_String'Access;
   Dash_margs_String : aliased  String := "-margs";
   Dash_margs        : constant String_Access := Dash_margs_String'Access;
   Dash_o_String     : aliased  String := "-o";
   Dash_o            : constant String_Access := Dash_o_String'Access;
   Dash_P_String     : aliased  String := "-P";
   Dash_P            : constant String_Access := Dash_P_String'Access;
   Dash_q_String     : aliased  String := "-q";
   Dash_q            : constant String_Access := Dash_q_String'Access;
   Dash_u_String     : aliased  String := "-u";
   Dash_u            : constant String_Access := Dash_u_String'Access;
   Dash_v_String     : aliased  String := "-v";
   Dash_v            : constant String_Access := Dash_v_String'Access;
   Dash_vP1_String   : aliased  String := "-vP1";
   Dash_vP1          : constant String_Access := Dash_vP1_String'Access;
   Dash_vP2_String   : aliased  String := "-vP2";
   Dash_vP2          : constant String_Access := Dash_vP2_String'Access;
   Dash_x_String     : aliased  String := "-x";
   Dash_x            : constant String_Access := Dash_x_String'Access;
   r_String          : aliased  String := "r";
   r                 : constant String_Access := r_String'Access;

   CPATH : constant String := "CPATH";
   --  The environment variable to set when compiler is a GCC compiler
   --  to indicate the include directory path.

   Current_Include_Paths : array (Programming_Language) of String_Access;
   --  A cache for the paths of included directories, to avoid setting
   --  env var CPATH unnecessarily.

   C_Plus_Plus_Is_Used : Boolean := False;
   --  True when there are sources in C++

   Link_Options_Switches : Argument_List_Access := null;
   --  The link options coming from the attributes Linker'Linker_Options in
   --  project files imported, directly or indirectly, by the main project.

   Total_Number_Of_Errors : Natural := 0;
   --  Used when Keep_Going is True (switch -k) to keep the total number
   --  of compilation/linking errors, to report at the end of execution.

   Error_Header : constant String := "*** ERROR: ";
   --  The beginning of error message, when Keep_Going is True

   Need_To_Relink : Boolean := False;
   --  True when an executable of a language other than Ada need to be linked

   Path_Option : String_Access;
   --  The path option switch, when supported

   package Lib_Path is new Table.Table
     (Table_Component_Type => Character,
      Table_Index_Type     => Integer,
      Table_Low_Bound      => 1,
      Table_Initial        => 200,
      Table_Increment      => 50,
      Table_Name           => "Makegpr.Lib_Path");
   --  A table to compute the path to put in the path option switch, when it
   --  is supported.

   procedure Add_Archives (For_Gnatmake : Boolean);
   --  Add to Arguments the list of archives for linking an executable

   procedure Add_Argument (Arg : String_Access; Display : Boolean);
   procedure Add_Argument (Arg : String; Display : Boolean);
   --  Add an argument to Arguments. Reallocate if necessary.

   procedure Add_Arguments (Args : Argument_List; Display : Boolean);
   --  Add a list of arguments to Arguments. Reallocate if necessary

   procedure Add_Option (Arg : String);
   --  Add a switch for the Ada, C or C++ compiler, or for the linker.
   --  The table where this option is stored depends on the values of
   --  Current_Processor and Current_Language.

   procedure Add_Search_Directories
     (Data : Project_Data; Language : Programming_Language);
   --  Either add to the Arguments the necessary -I switches needed to
   --  compile, or, when compiler is gcc/g++, set up the C*INCLUDE_PATH
   --  environment variable, if necessary.

   procedure Add_Source_Id (Id : Other_Source_Id);
   --  Add a source id to Source_Indexes, with Found set to False

   procedure Add_Switches
     (Data      : Project_Data;
      Proc      : Processor;
      Language  : Other_Programming_Language;
      File_Name : Name_Id);
   --  Add to Arguments the switches, if any, for a source (attribute Switches)
   --  or language (attribute Default_Switches), coming from package Compiler
   --  or Linker (depending on Proc) of a specified project file.

   procedure Build_Archive (Project : Project_Id; Unconditionally : Boolean);
   --  Build the archive for a specified project. If Unconditionally is
   --  False, first check if the archive is up to date, and build it only
   --  if it is not.

   procedure Check_Compilation_Needed
     (Source          : Other_Source;
      Need_To_Compile : out Boolean);
   --  Check if a source of a language other than Ada needs to be compiled or
   --  recompiled.

   procedure Check_For_C_Plus_Plus;
   --  Check if C++ is used in at least one project

   procedure Compile
     (Source_Id    : Other_Source_Id;
      Data         : Project_Data;
      Local_Errors : in out Boolean);

   procedure Compile_Individual_Sources;
   --  Compile the sources specified on the command line, when in
   --  Unique_Compile mode.

   procedure Compile_Link_With_Gnatmake (Mains_Specified : Boolean);
   --  Compile/Link with gnatmake when there are Ada sources in the main
   --  project. Arguments may already contain options to be used by
   --  gnatmake. Used for both Ada mains and mains of other languages.
   --  When Compile_Only is True, do not use the linking options

   procedure Compile_Sources;
   --  Compile the sources of languages other than Ada, if necessary

   procedure Copyright;
   --  Output the Copyright notice

   procedure Create_Archive_Dependency_File
     (Name         : String;
      First_Source : Other_Source_Id);
   --  ??? needs comment

   procedure Display_Command
     (Name  : String;
      Path  : String_Access;
      CPATH : String_Access := null);
   --  Display the command for a spawned process, if in Verbose_Mode or
   --  not in Quiet_Output.

   procedure Get_Compiler (For_Language : Programming_Language);
   --  Find the compiler name and path name for a specified programming
   --  language, if not already done. Results are in the corresponding
   --  elements of arrays Compiler_Names and Compiler_Paths. Name of compiler
   --  is found in package IDE of the main project, or defaulted.
   --  Fail if compiler cannot be found on the path. For the Ada language,
   --  gnatmake, rather than the Ada compiler is returned.

   procedure Get_Imported_Directories
     (Project : Project_Id;
      Data    : in out Project_Data);
   --  Find the necessary switches -I to be used when compiling sources
   --  of languages other than Ada, in a specified project file. Cache the
   --  result in component Imported_Directories_Switches of the project data.
   --  For gcc/g++ compilers, get the value of the C*_INCLUDE_PATH, instead.

   procedure Initialize;
   --  Do the necessary package initialization and process the command line
   --  arguments.

   procedure Link_Executables;
   --  Link executables

   procedure Report_Error (S1 : String; S2 : String := ""; S3 : String := "");
   --  Report an error. If Keep_Going is False, just call Osint.Fail.
   --  If Keep_Going is True, display the error and increase the total number
   --  of errors.

   procedure Report_Total_Errors (Kind : String);
   --  If Total_Number_Of_Errors is not zero, report it, and fail

   procedure Scan_Arg (Arg : String);
   --  Process one command line argument

   function Strip_CR_LF (Text : String) return String;
   --  Needs comment ???

   procedure Usage;
   --  Display the usage

   ------------------
   -- Add_Archives --
   ------------------

   procedure Add_Archives (For_Gnatmake : Boolean) is
      Last_Arg : constant Natural := Last_Argument;
      --  The position of the last argument before adding the archives.
      --  Used to reverse the order of the arguments added when processing
      --  the archives.

      procedure Recursive_Add_Archives (Project : Project_Id);
      --  Recursive procedure to add the archive of a project file, if any,
      --  then call itself for the project imported.

      ----------------------------
      -- Recursive_Add_Archives --
      ----------------------------

      procedure Recursive_Add_Archives (Project : Project_Id) is
         Data     : Project_Data;
         Imported : Project_List;
         Prj      : Project_Id;

      begin
         --  Nothing to do when there is no project specified

         if Project /= No_Project then
            Data := Projects.Table (Project);

            --  Nothing to do if the project has already been processed

            if not Data.Seen then

               --  Mark the project as processed, to avoid processing it again

               Projects.Table (Project).Seen := True;

               Recursive_Add_Archives (Data.Extends);

               Imported := Data.Imported_Projects;

               --  Call itself recursively for all imported projects

               while Imported /= Empty_Project_List loop
                  Prj := Project_Lists.Table (Imported).Project;

                  if Prj /= No_Project then
                     while Projects.Table (Prj).Extended_By /= No_Project loop
                        Prj := Projects.Table (Prj).Extended_By;
                     end loop;

                     Recursive_Add_Archives (Prj);
                  end if;

                  Imported := Project_Lists.Table (Imported).Next;
               end loop;

               --  If there is sources of language other than Ada in this
               --  project, add the path of the archive to Arguments.

               if Data.Sources_Present then
                  if Data.Library then

                     --  If it is a library project file, nothing to do if
                     --  gnatmake will be invoked, because gnatmake will take
                     --  care of it, even if the library is not an Ada library.

                     if not For_Gnatmake then
                        if Data.Library_Kind = Static then
                           Add_Argument
                             (Get_Name_String (Data.Library_Dir) &
                              Directory_Separator &
                              "lib" & Get_Name_String (Data.Library_Name) &
                              '.' & Archive_Ext,
                              Verbose_Mode);

                        else
                           --  As we first insert in the reverse order,
                           --  -L<dir> is put after -l<lib>

                           Add_Argument
                             ("-l" & Get_Name_String (Data.Library_Name),
                              Verbose_Mode);

                           Get_Name_String (Data.Library_Dir);

                           Add_Argument
                             ("-L" & Name_Buffer (1 .. Name_Len),
                              Verbose_Mode);

                           --  If there is a run path option, prepend this
                           --  directory to the library path. It is probable
                           --  that the order of the directories in the path
                           --  option is not important, but just in case
                           --  put the directories in the same order as the
                           --  libraries.

                           if Path_Option /= null then
                              --  If it is not the first directory, make room
                              --  at the beginning of the table, including
                              --  for a path separator.

                              if Lib_Path.Last > 0 then
                                 declare
                                    Increment : constant Positive :=
                                                  Name_Len + 1;
                                    Prev_Last : constant Positive :=
                                                  Lib_Path.Last;

                                 begin
                                    Lib_Path.Set_Last (Prev_Last + Increment);

                                    for Index in reverse 1 .. Prev_Last loop
                                       Lib_Path.Table (Index + Increment) :=
                                         Lib_Path.Table (Index);
                                    end loop;

                                    Lib_Path.Table (Increment) :=
                                      Path_Separator;
                                 end;

                              else
                                 --  If it is the first directory, just set
                                 --  Last to the length of the directory.

                                 Lib_Path.Set_Last (Name_Len);
                              end if;

                              --  Put the directory at the beginning of the
                              --  table.

                              for Index in 1 .. Name_Len loop
                                 Lib_Path.Table (Index) := Name_Buffer (Index);
                              end loop;
                           end if;
                        end if;
                     end if;

                  else
                     --  For a non library project, just add the path name of
                     --  the archive.

                     Add_Argument
                       (Get_Name_String (Data.Object_Directory) &
                        Directory_Separator &
                        "lib" & Get_Name_String (Data.Name) &
                        '.' & Archive_Ext,
                        Verbose_Mode);
                  end if;
               end if;
            end if;
         end if;
      end Recursive_Add_Archives;

   begin
      --  First, mark all projects as not processed

      for Project in 1 .. Projects.Last loop
         Projects.Table (Project).Seen := False;
      end loop;

      --  Take care of the run path option

      if Path_Option = null then
         Path_Option := MLib.Linker_Library_Path_Option;
      end if;

      Lib_Path.Set_Last (0);

      --  Add archives in the reverse order

      Recursive_Add_Archives (Main_Project);

      --  And reverse the order

      declare
         First : Positive := Last_Arg + 1;
         Last  : Natural  := Last_Argument;
         Temp  : String_Access;

      begin
         while First < Last loop
            Temp := Arguments (First);
            Arguments (First) := Arguments (Last);
            Arguments (Last)  := Temp;
            First := First + 1;
            Last := Last - 1;
         end loop;
      end;
   end Add_Archives;

   ------------------
   -- Add_Argument --
   ------------------

   procedure Add_Argument (Arg : String_Access; Display : Boolean) is
   begin
      --  Nothing to do if no argument is specified or if argument is empty

      if Arg /= null or else Arg'Length = 0 then

         --  Reallocate arrays if necessary

         if Last_Argument = Arguments'Last then
            declare
               New_Arguments : constant Argument_List_Access :=
                                 new Argument_List
                                   (1 .. Last_Argument +
                                           Initial_Argument_Count);

               New_Arguments_Displayed : constant Booleans :=
                                           new Boolean_Array
                                             (1 .. Last_Argument +
                                                     Initial_Argument_Count);

            begin
               New_Arguments (Arguments'Range) := Arguments.all;

               --  To avoid deallocating the strings, nullify all components
               --  of Arguments before calling Free.

               Arguments.all := (others => null);

               Free (Arguments);
               Arguments := New_Arguments;

               New_Arguments_Displayed (Arguments_Displayed'Range) :=
                 Arguments_Displayed.all;
               Free (Arguments_Displayed);
               Arguments_Displayed := New_Arguments_Displayed;
            end;
         end if;

         --  Add the argument and its display indication

         Last_Argument := Last_Argument + 1;
         Arguments (Last_Argument) := Arg;
         Arguments_Displayed (Last_Argument) := Display;
      end if;
   end Add_Argument;

   procedure Add_Argument (Arg : String; Display : Boolean) is
      Argument : String_Access := null;

   begin
      --  Nothing to do if argument is empty

      if Arg'Length > 0 then
         --  Check if the argument is already in the Cache_Args table.
         --  If it is already there, reuse the allocated value.

         for Index in 1 .. Cache_Args.Last loop
            if Cache_Args.Table (Index).all = Arg then
               Argument := Cache_Args.Table (Index);
               exit;
            end if;
         end loop;

         --  If the argument is not in the cache, create a new entry in the
         --  cache.

         if Argument = null then
            Argument := new String'(Arg);
            Cache_Args.Increment_Last;
            Cache_Args.Table (Cache_Args.Last) := Argument;
         end if;

         --  And add the argument

         Add_Argument (Argument, Display);
      end if;
   end Add_Argument;

   -------------------
   -- Add_Arguments --
   -------------------

   procedure Add_Arguments (Args : Argument_List; Display : Boolean) is
   begin
      --  Reallocate the arrays, if necessary

      if Last_Argument + Args'Length > Arguments'Last then
         declare
            New_Arguments : constant Argument_List_Access :=
              new Argument_List
                (1 .. Last_Argument + Args'Length + Initial_Argument_Count);
            New_Arguments_Displayed : constant Booleans :=
              new Boolean_Array
                (1 .. Last_Argument + Args'Length + Initial_Argument_Count);

         begin
            New_Arguments (1 .. Last_Argument) :=
              Arguments (1 .. Last_Argument);

            --  To avoid deallocating the strings, nullify all components
            --  of Arguments before calling Free.

            Arguments.all := (others => null);
            Free (Arguments);

            Arguments := New_Arguments;
            New_Arguments_Displayed (1 .. Last_Argument) :=
              Arguments_Displayed (1 .. Last_Argument);
            Free (Arguments_Displayed);
            Arguments_Displayed := New_Arguments_Displayed;
         end;
      end if;

      --  Add the new arguments and the display indications

      Arguments (Last_Argument + 1 .. Last_Argument + Args'Length) := Args;
      Arguments_Displayed (Last_Argument + 1 .. Last_Argument + Args'Length) :=
        (others => Display);
      Last_Argument := Last_Argument + Args'Length;
   end Add_Arguments;

   ----------------
   -- Add_Option --
   ----------------

   procedure Add_Option (Arg : String) is
      Option : constant String_Access := new String'(Arg);

   begin
      case Current_Processor is
         when None =>
            null;

         when Linker =>

            --  Add option to the linker table

            Linker_Options.Increment_Last;
            Linker_Options.Table (Linker_Options.Last) := Option;

         when Compiler =>

            --  Add option to the compiler option table, depending on the
            --  value of Current_Language.

            Comp_Opts.Increment_Last (Options (Current_Language));
            Options (Current_Language).Table
              (Comp_Opts.Last (Options (Current_Language))) := Option;

      end case;
   end Add_Option;

   -------------------
   -- Add_Source_Id --
   -------------------

   procedure Add_Source_Id (Id : Other_Source_Id) is
   begin
      --  Reallocate the array, if necessary

      if Last_Source = Source_Indexes'Last then
         declare
            New_Indexes : constant Source_Indexes_Ref :=
                            new Source_Index_Array
                              (1 .. Source_Indexes'Last +
                                      Initial_Source_Index_Count);
         begin
            New_Indexes (Source_Indexes'Range) := Source_Indexes.all;
            Free (Source_Indexes);
            Source_Indexes := New_Indexes;
         end;
      end if;

      Last_Source := Last_Source + 1;
      Source_Indexes (Last_Source) := (Id, False);
   end Add_Source_Id;

   ----------------------------
   -- Add_Search_Directories --
   ----------------------------

   procedure Add_Search_Directories
     (Data     : Project_Data;
      Language : Programming_Language)
   is
   begin
      --  If a GNU compiler is used, set the CPATH environment variable,
      --  if it does not already has the correct value.

      if Compiler_Is_Gcc (Language) then
         if Current_Include_Paths (Language) /= Data.Include_Path then
            Current_Include_Paths (Language) := Data.Include_Path;
            Setenv (CPATH, Data.Include_Path.all);
         end if;

      else
         Add_Arguments (Data.Imported_Directories_Switches.all, Verbose_Mode);
      end if;
   end Add_Search_Directories;

   ------------------
   -- Add_Switches --
   ------------------

   procedure Add_Switches
     (Data      : Project_Data;
      Proc      : Processor;
      Language  : Other_Programming_Language;
      File_Name : Name_Id)
   is
      Switches       : Variable_Value;
      --  The switches, if any, for the file/language

      Pkg            : Package_Id;
      --  The id of the package where to look for the switches

      Defaults       : Array_Element_Id;
      --  The Default_Switches associative array

      Switches_Array : Array_Element_Id;
      --  The Switches associative array

      Element_Id     : String_List_Id;
      Element        : String_Element;

   begin
      --  First, choose the proper package

      case Proc is
         when None =>
            raise Program_Error;

         when Linker =>
            Pkg := Value_Of (Name_Linker, Data.Decl.Packages);

         when Compiler =>
            Pkg := Value_Of (Name_Compiler, Data.Decl.Packages);
      end case;

      --  Get the Switches ("file name"), if they exist

      Switches_Array := Prj.Util.Value_Of
        (Name      => Name_Switches,
         In_Arrays =>
           Packages.Table (Pkg).Decl.Arrays);

      Switches :=
        Prj.Util.Value_Of
          (Index     => File_Name,
           Src_Index => 0,
           In_Array  => Switches_Array);

      --  Otherwise, get the Default_Switches ("language"), if they exist

      if Switches = Nil_Variable_Value then
         Defaults := Prj.Util.Value_Of
           (Name      => Name_Default_Switches,
            In_Arrays => Packages.Table (Pkg).Decl.Arrays);
         Switches := Prj.Util.Value_Of
           (Index     => Lang_Name_Ids (Language),
            Src_Index => 0,
            In_Array  => Defaults);
      end if;

      --  If there are switches, add them to Arguments

      if Switches /= Nil_Variable_Value then
         Element_Id := Switches.Values;

         while Element_Id /= Nil_String loop
            Element := String_Elements.Table (Element_Id);

            if Element.Value /= No_Name then
               Add_Argument (Get_Name_String (Element.Value), True);
            end if;

            Element_Id := Element.Next;
         end loop;
      end if;
   end Add_Switches;

   -------------------
   -- Build_Archive --
   -------------------

   procedure Build_Archive (Project : Project_Id; Unconditionally : Boolean) is
      Data      : constant Project_Data := Projects.Table (Project);
      Source_Id : Other_Source_Id;
      Source    : Other_Source;
      Success   : Boolean;

      Archive_Name : constant String :=
        "lib" & Get_Name_String (Data.Name) & '.' & Archive_Ext;
      --  The name of the archive file for this project

      Archive_Dep_Name : constant String :=
        "lib" & Get_Name_String (Data.Name) & ".deps";
      --  The name of the archive dependency file for this project

      Need_To_Rebuild : Boolean := Unconditionally;
      --  When True, archive will be rebuilt

      File : Prj.Util.Text_File;

      Object_Name : Name_Id;
      Time_Stamp  : Time_Stamp_Type;

      Saved_Last_Argument : Natural;

   begin
      --  First, make sure that the archive builder (ar) is on the path

      if Archive_Builder_Path = null then
         Archive_Builder_Path := Locate_Exec_On_Path (Archive_Builder);

         if Archive_Builder_Path = null then
            Osint.Fail
              ("unable to locate archive builder """,
               Archive_Builder,
               """");
         end if;

         --  If there is an archive indexer (ranlib), try to locate it on the
         --  path. Don't fail if it is not found.

         if Archive_Indexer /= "" then
            Archive_Indexer_Path := Locate_Exec_On_Path (Archive_Indexer);
         end if;
      end if;

      --  If Unconditionally is False, check if the archive need to be built

      if not Need_To_Rebuild then
         if Verbose_Mode then
            Write_Str  ("   Checking ");
            Write_Line (Archive_Name);
         end if;

         --  If the archive does not exist, of course it needs to be built

         if not Is_Regular_File (Archive_Name) then
            Need_To_Rebuild := True;

            if Verbose_Mode then
               Write_Line ("      -> archive does not exist");
            end if;

         --  Archive does exist

         else
            --  Check the archive dependency file

            Open (File, Archive_Dep_Name);

            --  If the archive dependency file does not exist, we need to
            --  to rebuild the archive and to create its dependency file.

            if not Is_Valid (File) then
               Need_To_Rebuild := True;

               if Verbose_Mode then
                  Write_Str  ("      -> archive dependency file ");
                  Write_Str  (Archive_Dep_Name);
                  Write_Line (" does not exist");
               end if;

            else
               --  Put all sources of language other than Ada in
               --  Source_Indexes.

               Last_Source := 0;
               Source_Id := Data.First_Other_Source;

               while Source_Id /= No_Other_Source loop
                  Add_Source_Id (Source_Id);
                  Source_Id := Other_Sources.Table (Source_Id).Next;
               end loop;

               --  Read the dependency file, line by line

               while not End_Of_File (File) loop
                  Get_Line (File, Name_Buffer, Name_Len);

                  --  First line is the name of an object file

                  Object_Name := Name_Find;
                  Source_Id := No_Other_Source;

                  --  Check if this object file is for a source of this project

                  for S in 1 .. Last_Source loop
                     if (not Source_Indexes (S).Found) and then
                       Other_Sources.Table
                         (Source_Indexes (S).Id).Object_Name =
                       Object_Name
                     then
                        --  We have found the object file: get the source
                        --  data, and mark it as found.

                        Source_Id := Source_Indexes (S).Id;
                        Source := Other_Sources.Table (Source_Id);
                        Source_Indexes (S).Found := True;
                        exit;
                     end if;
                  end loop;

                  --  If it is not for a source of this project, then the
                  --  archive needs to be rebuilt.

                  if Source_Id = No_Other_Source then
                     Need_To_Rebuild := True;
                     if Verbose_Mode then
                        Write_Str  ("      -> ");
                        Write_Str  (Get_Name_String (Object_Name));
                        Write_Line (" is not an object of the project");
                     end if;

                     exit;
                  end if;

                  --  The second line is the time stamp of the object file.
                  --  If there is no next line, then the dependency file is
                  --  truncated, and the archive need to be rebuilt.

                  if End_Of_File (File) then
                     Need_To_Rebuild := True;

                     if Verbose_Mode then
                        Write_Str  ("      -> archive dependency file ");
                        Write_Line (" is truncated");
                     end if;

                     exit;
                  end if;

                  Get_Line (File, Name_Buffer, Name_Len);

                  --  If the line has the wrong number of character, then
                  --  the dependency file is incorrectly formatted, and the
                  --  archive needs to be rebuilt.

                  if Name_Len /= Time_Stamp_Length then
                     Need_To_Rebuild := True;

                     if Verbose_Mode then
                        Write_Str  ("      -> archive dependency file ");
                        Write_Line (" is incorrectly formatted (time stamp)");
                     end if;

                     exit;
                  end if;

                  Time_Stamp := Time_Stamp_Type (Name_Buffer (1 .. Name_Len));

                  --  If the time stamp in the dependency file is different
                  --  from the time stamp of the object file, then the archive
                  --  needs to be rebuilt.

                  if Time_Stamp /= Source.Object_TS then
                     Need_To_Rebuild := True;

                     if Verbose_Mode then
                        Write_Str  ("      -> time stamp of ");
                        Write_Str  (Get_Name_String (Object_Name));
                        Write_Str  (" is incorrect in the archive");
                        Write_Line (" dependency file");
                     end if;

                     exit;
                  end if;
               end loop;

               Close (File);

               if not Need_To_Rebuild then

                  --  Now, check if all object files of the project have been
                  --  accounted for. If any of them is not in the dependency
                  --  file, the archive needs to be rebuilt.

                  for Index in 1 .. Last_Source loop
                     if not Source_Indexes (Index).Found then
                        Need_To_Rebuild := True;

                        if Verbose_Mode then
                           Source_Id := Source_Indexes (Index).Id;
                           Source := Other_Sources.Table (Source_Id);
                           Write_Str  ("      -> ");
                           Write_Str  (Get_Name_String (Source.Object_Name));
                           Write_Str  (" is not in the archive ");
                           Write_Line ("dependency file");
                        end if;

                        exit;
                     end if;
                  end loop;
               end if;

               if (not Need_To_Rebuild) and Verbose_Mode then
                  Write_Line ("      -> up to date");
               end if;
            end if;
         end if;
      end if;

      --  Build the archive if necessary

      if Need_To_Rebuild then

         --  If an archive is built, then linking will need to occur
         --  unconditionally.

         Need_To_Relink := True;

         Last_Argument := 0;

         --  If it is a library project file, we need to build the library
         --  in the library directory.

         if Data.Library then

            --  If there are sources in Ada, then gnatmake will build the
            --  library, so nothing to do.

            if not Data.Languages (Lang_Ada) then

               --  Get all the object files of the project

               Source_Id := Data.First_Other_Source;

               while Source_Id /= No_Other_Source loop
                  Source := Other_Sources.Table (Source_Id);
                  Add_Argument
                    (Get_Name_String (Source.Object_Name), Verbose_Mode);
                  Source_Id := Source.Next;
               end loop;

               --  If it is a library, it need to be built it the same way
               --  Ada libraries are built.

               if Data.Library_Kind = Static then
                  MLib.Build_Library
                    (Ofiles => Arguments (1 .. Last_Argument),
                     Afiles => No_Argument,
                     Output_File => Get_Name_String (Data.Library_Name),
                     Output_Dir  => Get_Name_String (Data.Library_Dir));

               else
                  MLib.Tgt.Build_Dynamic_Library
                    (Ofiles       => Arguments (1 .. Last_Argument),
                     Foreign      => Arguments (1 .. Last_Argument),
                     Afiles       => No_Argument,
                     Options      => No_Argument,
                     Interfaces   => No_Argument,
                     Lib_Filename => Get_Name_String (Data.Library_Name),
                     Lib_Dir      => Get_Name_String (Data.Library_Dir),
                     Symbol_Data  => No_Symbols,
                     Driver_Name  => No_Name,
                     Lib_Address  => "",
                     Lib_Version  => "",
                     Relocatable  => Data.Library_Kind = Relocatable,
                     Auto_Init    => False);
               end if;
            end if;

            --  Create fake empty archive, so we can check its time stamp later

            declare
               Archive : Ada.Text_IO.File_Type;
               use Ada.Text_IO;
            begin
               Create (Archive, Out_File, Archive_Name);
               Close (Archive);
            end;

            Create_Archive_Dependency_File
              (Archive_Dep_Name, Data.First_Other_Source);

            return;
         end if;

         --  Start with the options found in MLib.Tgt (usually just "rc")

         Add_Arguments (Archive_Builder_Options.all, True);

         --  Followed by the archive name

         Add_Argument (Archive_Name, True);

         --  Followed by all the object files of the project

         Source_Id := Data.First_Other_Source;

         while Source_Id /= No_Other_Source loop
            Source := Other_Sources.Table (Source_Id);
            Add_Argument (Get_Name_String (Source.Object_Name), Verbose_Mode);
            Source_Id := Source.Next;
         end loop;

         --  Spawn the archive builder (ar)

         Saved_Last_Argument := Last_Argument;

         Last_Argument := Max_In_Archives;

         loop
            if Last_Argument > Saved_Last_Argument then
               Last_Argument := Saved_Last_Argument;
            end if;

            Display_Command (Archive_Builder, Archive_Builder_Path);

            Spawn
              (Archive_Builder_Path.all,
               Arguments (1 .. Last_Argument),
               Success);

            exit when not Success;

            exit when Last_Argument = Saved_Last_Argument;

            Arguments (1) := r;
            Arguments (3 .. Saved_Last_Argument - Last_Argument + 2) :=
              Arguments (Last_Argument + 1 .. Saved_Last_Argument);
            Saved_Last_Argument := Saved_Last_Argument - Last_Argument + 2;
         end loop;

         if Success then

            --  If the archive was built, run the archive indexer (ranlib),
            --  if there is one.

            if Archive_Indexer_Path /= null then
               Last_Argument := 0;
               Add_Argument (Archive_Name, True);

               Display_Command (Archive_Indexer, Archive_Indexer_Path);

               Spawn (Archive_Indexer_Path.all, Arguments (1 .. 1), Success);

               if not Success then

                  --  Running ranlib failed, delete the dependency file,
                  --  if it exists.

                  if Is_Regular_File (Archive_Dep_Name) then
                     Delete_File (Archive_Dep_Name, Success);
                  end if;

                  --  And report the error

                  Report_Error
                    ("running" & Archive_Indexer & " for project """,
                     Get_Name_String (Data.Name),
                     """ failed");
                  return;
               end if;
            end if;

            --  The archive was correctly built, create its dependency file

            Create_Archive_Dependency_File
              (Archive_Dep_Name, Data.First_Other_Source);

         else
            --  Building the archive failed, delete the dependency file, if
            --  one exists.

            if Is_Regular_File (Archive_Dep_Name) then
               Delete_File (Archive_Dep_Name, Success);
            end if;

            --  And report the error

            Report_Error
              ("building archive for project """,
               Get_Name_String (Data.Name),
               """ failed");
         end if;
      end if;
   end Build_Archive;

   ------------------------------
   -- Check_Compilation_Needed --
   ------------------------------

   procedure Check_Compilation_Needed
     (Source          : Other_Source;
      Need_To_Compile : out Boolean)
   is
      Source_Name : constant String := Get_Name_String (Source.File_Name);
      Source_Path : constant String := Get_Name_String (Source.Path_Name);
      Object_Name : constant String := Get_Name_String (Source.Object_Name);
      Dep_Name    : constant String := Get_Name_String (Source.Dep_Name);

      Source_In_Dependencies : Boolean := False;
      --  Set to True if the source was find in the dependency file of its
      --  object file.

      Dep_File : Prj.Util.Text_File;
      Start    : Natural;
      Finish   : Natural;

   begin
      --  Assume the worst, so that statement "return;" may be used if there
      --  is any problem.

      Need_To_Compile := True;

      if Verbose_Mode then
         Write_Str  ("   Checking ");
         Write_Str  (Source_Name);
         Write_Line (" ... ");
      end if;

      --  If the object file does not exist, of course the source need to be
      --  compiled.

      if Source.Object_TS = Empty_Time_Stamp then
         if Verbose_Mode then
            Write_Str  ("      -> object file ");
            Write_Str  (Object_Name);
            Write_Line (" does not exist");
         end if;

         return;
      end if;

      --  If the object file has been created before the last modification
      --  of the source, the source need to be recompiled.

      if Source.Object_TS < Source.Source_TS then
         if Verbose_Mode then
            Write_Str  ("      -> object file ");
            Write_Str  (Object_Name);
            Write_Line (" has time stamp earlier than source");
         end if;

         return;
      end if;

      --  If there is no dependency file, then the source needs to be
      --  recompiled and the dependency file need to be created.

      if Source.Dep_TS = Empty_Time_Stamp then
         if Verbose_Mode then
            Write_Str  ("      -> dependency file ");
            Write_Str  (Dep_Name);
            Write_Line (" does not exist");
         end if;

         return;
      end if;

      --  The source needs to be recompiled if the source has been modified
      --  after the dependency file has been created.

      if Source.Dep_TS < Source.Source_TS then
         if Verbose_Mode then
            Write_Str  ("      -> dependency file ");
            Write_Str  (Dep_Name);
            Write_Line (" has time stamp earlier than source");
         end if;

         return;
      end if;

      --  Look for all dependencies

      Open (Dep_File, Dep_Name);

      --  If dependency file cannot be open, we need to recompile the source

      if not Is_Valid (Dep_File) then
         if Verbose_Mode then
            Write_Str  ("      -> could not open dependency file ");
            Write_Line (Dep_Name);
         end if;

         return;
      end if;

      declare
         End_Of_File_Reached : Boolean := False;

      begin
         loop
            if End_Of_File (Dep_File) then
               End_Of_File_Reached := True;
               exit;
            end if;

            Get_Line (Dep_File, Name_Buffer, Name_Len);

            exit when Name_Len > 0 and then Name_Buffer (1) /= '#';
         end loop;

         --  If dependency file contains only empty lines or comments, then
         --  the dependencies are unknown, and the source needs to be
         --  recompiled.

         if End_Of_File_Reached then
            if Verbose_Mode then
               Write_Str  ("      -> dependency file ");
               Write_Str  (Dep_Name);
               Write_Line (" is empty");
            end if;

            Close (Dep_File);
            return;
         end if;
      end;

      Start  := 1;
      Finish := Index (Name_Buffer (1 .. Name_Len), ": ");

      --  The first line must start with the name of the object file, followed
      --  by a colon (:).

      if Finish = 0 or else Name_Buffer (1 .. Finish - 1) /= Object_Name then
         if Verbose_Mode then
            Write_Str  ("      -> dependency file ");
            Write_Str  (Dep_Name);
            Write_Line (" has wrong format");
         end if;

         Close (Dep_File);
         return;

      else
         Start := Finish + 2;

         --  Process each line

         Line_Loop : loop
            declare
               Line : constant String := Name_Buffer (1 .. Name_Len);
               Last : constant Natural := Name_Len;

            begin
               Name_Loop : loop

                  --  Find the beginning of the next source path name

                  while Start < Last and then Line (Start) = ' ' loop
                     Start := Start + 1;
                  end loop;

                  --  Go to next line when there is a continuation character \
                  --  at the end of the line.

                  exit Name_Loop when Start = Last
                                   and then Line (Start) = '\';

                  --  We should not be at the end of the line, without
                  --  a continuation character \.

                  if Start = Last then
                     if Verbose_Mode then
                        Write_Str  ("      -> dependency file ");
                        Write_Str  (Dep_Name);
                        Write_Line (" has wrong format");
                     end if;

                     Close (Dep_File);
                     return;
                  end if;

                  --  Look for the end of the source path name

                  Finish := Start;
                  while Finish < Last and then Line (Finish + 1) /= ' ' loop
                     Finish := Finish + 1;
                  end loop;

                  --  Check this source

                  declare
                     Src_Name : constant String :=
                                  Normalize_Pathname
                                    (Name           => Line (Start .. Finish),
                                     Case_Sensitive => False);
                     Src_TS   : Time_Stamp_Type;

                  begin
                     --  If it is original source, set Source_In_Dependencies

                     if Src_Name = Source_Path then
                        Source_In_Dependencies := True;
                     end if;

                     Name_Len := 0;
                     Add_Str_To_Name_Buffer (Src_Name);
                     Src_TS := File_Stamp (Name_Find);

                     --  If the source does not exist, we need to recompile

                     if Src_TS = Empty_Time_Stamp then
                        if Verbose_Mode then
                           Write_Str  ("      -> source ");
                           Write_Str  (Src_Name);
                           Write_Line (" does not exist");
                        end if;

                        Close (Dep_File);
                        return;

                     --  If the source has been modified after the object file,
                     --  we need to recompile.

                     elsif Src_TS > Source.Object_TS then
                        if Verbose_Mode then
                           Write_Str  ("      -> source ");
                           Write_Str  (Src_Name);
                           Write_Line
                             (" has time stamp later than object file");
                        end if;

                        Close (Dep_File);
                        return;
                     end if;
                  end;

                  --  If the source path name ends the line, we are done.

                  exit Line_Loop when Finish = Last;

                  --  Go get the next source on the line

                  Start := Finish + 1;
               end loop Name_Loop;
            end;

            --  If we are here, we had a continuation character \ at the end
            --  of the line, so we continue with the next line.

            Get_Line (Dep_File, Name_Buffer, Name_Len);
            Start := 1;
         end loop Line_Loop;
      end if;

      Close (Dep_File);

      --  If the original sources were not in the dependency file, then we
      --  need to recompile. It may mean that we are using a different source
      --  (different variant) for this object file.

      if not Source_In_Dependencies then
         if Verbose_Mode then
            Write_Str  ("      -> source ");
            Write_Str  (Source_Path);
            Write_Line (" is not in the dependencies");
         end if;

         return;
      end if;

      --  If we are here, then everything is OK, and we don't need
      --  to recompile.

      if Verbose_Mode then
         Write_Line ("      -> up to date");
      end if;

      Need_To_Compile := False;
   end Check_Compilation_Needed;

   ---------------------------
   -- Check_For_C_Plus_Plus --
   ---------------------------

   procedure Check_For_C_Plus_Plus is
   begin
      C_Plus_Plus_Is_Used := False;

      for Project in 1 .. Projects.Last loop
         if Projects.Table (Project).Languages (Lang_C_Plus_Plus) then
            C_Plus_Plus_Is_Used := True;
            exit;
         end if;
      end loop;
   end Check_For_C_Plus_Plus;

   -------------
   -- Compile --
   -------------

   procedure Compile
     (Source_Id    : Other_Source_Id;
      Data         : in Project_Data;
      Local_Errors : in out Boolean)
   is
      Source  : Other_Source := Other_Sources.Table (Source_Id);
      Success : Boolean;
      CPATH   : String_Access := null;

   begin
      --  If the compiler is not know yet, get its path name

      if Compiler_Names (Source.Language) = null then
         Get_Compiler (Source.Language);
      end if;

      --  For non GCC compilers, get the dependency file, calling first the
      --  compiler with the switch -M.

      if not Compiler_Is_Gcc (Source.Language) then
         Last_Argument := 0;

         --  Add the source name, preceded by -M

         Add_Argument (Dash_M, True);
         Add_Argument (Get_Name_String (Source.Path_Name), True);

         --  Add the compiling switches for this source found in
         --  package Compiler of the project file, if they exist.

         Add_Switches
           (Data, Compiler, Source.Language, Source.File_Name);

         --  Add the compiling switches for the language specified
         --  on the command line, if any.

         for
           J in 1 .. Comp_Opts.Last (Options (Source.Language))
         loop
            Add_Argument (Options (Source.Language).Table (J), True);
         end loop;

         --  Finally, add the imported directory switches for this
         --  project file.

         Add_Search_Directories (Data, Source.Language);

         --  And invoke the compiler using GNAT.Expect

         Display_Command
           (Compiler_Names (Source.Language).all,
            Compiler_Paths (Source.Language));

         begin
            Non_Blocking_Spawn
              (FD,
               Compiler_Paths (Source.Language).all,
               Arguments (1 .. Last_Argument),
               Buffer_Size => 0,
               Err_To_Out => True);

            declare
               Dep_File : Ada.Text_IO.File_Type;
               Result   : Expect_Match;
               Status   : Integer;

            begin
               --  Create the dependency file

               Create (Dep_File, Out_File, Get_Name_String (Source.Dep_Name));

               loop
                  Expect (FD, Result, Line_Matcher);

                  exit when Result = Expect_Timeout;

                  declare
                     S : constant String := Strip_CR_LF (Expect_Out (FD));

                  begin
                     --  Each line of the output is put in the dependency
                     --  file, including errors. If there are errors, the
                     --  syntax of the dependency file will be incorrect and
                     --  recompilation will occur automatically the next time
                     --  the dependencies are checked.

                     Put_Line (Dep_File, S);
                  end;
               end loop;

               --  If we are here, it means we had a timeout, so the
               --  dependency file may be incomplete. It is safer to
               --  delete it, otherwise the dependencies may be wrong.

               Close (FD, Status);
               Close (Dep_File);
               Delete_File (Get_Name_String (Source.Dep_Name), Success);

            exception
            when Process_Died =>

                  --  This is the normal outcome. Just close the file

                  Close (FD, Status);
                  Close (Dep_File);

            when others =>

                  --  Something wrong happened. It is safer to delete the
                  --  dependency file, otherwise the dependencies may be wrong.

                  Close (FD, Status);

                  if Is_Open (Dep_File) then
                     Close (Dep_File);
                  end if;

                  Delete_File (Get_Name_String (Source.Dep_Name), Success);
            end;

         exception
               --  If we cannot spawn the compiler, then the dependencies are
               --  not updated. It is safer then to delete the dependency file,
               --  otherwise the dependencies may be wrong.

            when Invalid_Process =>
               Delete_File (Get_Name_String (Source.Dep_Name), Success);
         end;
      end if;

      Last_Argument := 0;

      --  For GCC compilers, make sure the language is always specified to
      --  to the GCC driver, in case the extension is not recognized by the
      --  GCC driver as a source of the language.

      if Compiler_Is_Gcc (Source.Language) then
         Add_Argument (Dash_x, Verbose_Mode);
         Add_Argument
           (Lang_Names (Source.Language), Verbose_Mode);
      end if;

      --  Specify the source to be compiled

      Add_Argument (Dash_c, True);
      Add_Argument (Get_Name_String (Source.Path_Name), True);

      --  If non static library project, compile with the PIC option if there
      --  is one (when there is no PIC option, function MLib.Tgt.PIC_Option
      --  returns an empty string, and Add_Argument with an empty string has
      --  no effect).

      if Data.Library and then Data.Library_Kind /= Static then
         Add_Argument (PIC_Option, True);
      end if;

      --  Indicate the name of the object

      Add_Argument (Dash_o, True);
      Add_Argument (Get_Name_String (Source.Object_Name), True);

      --  When compiler is GCC, use the magic switch that creates
      --  the dependency file in the correct format.

      if Compiler_Is_Gcc (Source.Language) then
         Add_Argument
           ("-Wp,-MD," & Get_Name_String (Source.Dep_Name),
            Verbose_Mode);
      end if;

      --  Add the compiling switches for this source found in
      --  package Compiler of the project file, if they exist.

      Add_Switches
        (Data, Compiler, Source.Language, Source.File_Name);

      --  Add the compiling switches for the language specified
      --  on the command line, if any.

      for
        J in 1 .. Comp_Opts.Last (Options (Source.Language))
      loop
         Add_Argument (Options (Source.Language).Table (J), True);
      end loop;

      --  Finally, add the imported directory switches for this
      --  project file (or, for gcc compilers, set up the CPATH env var
      --  if needed).

      Add_Search_Directories (Data, Source.Language);

      --  Set CPATH, if compiler is GCC

      if Compiler_Is_Gcc (Source.Language) then
         CPATH := Current_Include_Paths (Source.Language);
      end if;

      --  And invoke the compiler

      Display_Command
        (Name  => Compiler_Names (Source.Language).all,
         Path  => Compiler_Paths (Source.Language),
         CPATH => CPATH);

      Spawn
        (Compiler_Paths (Source.Language).all,
         Arguments (1 .. Last_Argument),
         Success);

      if Success then

         --  Compilation was successful, update the time stamp
         --  of the object file.

         Source.Object_TS := File_Stamp (Source.Object_Name);

         --  Do some sanity checks

         if Source.Object_TS = Empty_Time_Stamp then
            Local_Errors := True;
            Report_Error
              ("object file ",
               Get_Name_String (Source.Object_Name),
               " has not been created");

         elsif Source.Object_TS < Source.Source_TS then
            Local_Errors := True;
            Report_Error
              ("object file ",
               Get_Name_String (Source.Object_Name),
               " has not been modified");

         else
            --  Everything looks fine, update the Other_Sources table

            Other_Sources.Table (Source_Id) := Source;
         end if;

      else
         Local_Errors := True;
         Report_Error
           ("compilation of ",
            Get_Name_String (Source.Path_Name),
            " failed");
      end if;
   end Compile;

   --------------------------------
   -- Compile_Individual_Sources --
   --------------------------------

   procedure Compile_Individual_Sources is
      Data         : Project_Data := Projects.Table (Main_Project);
      Source_Id    : Other_Source_Id;
      Source       : Other_Source;
      Source_Name  : Name_Id;
      Project_Name : String := Get_Name_String (Data.Name);
      Dummy        : Boolean := False;

      Ada_Is_A_Language : constant Boolean := Data.Languages (Lang_Ada);

   begin
      Ada_Mains.Init;

      To_Mixed (Project_Name);

      Compile_Only := True;

      Get_Imported_Directories (Main_Project, Data);
      Projects.Table (Main_Project) := Data;

      --  Compilation will occur in the object directory

      Change_Dir (Get_Name_String (Data.Object_Directory));

      if not Data.Sources_Present then
         if Ada_Is_A_Language then
            Mains.Reset;

            loop
               declare
                  Main : constant String := Mains.Next_Main;
               begin
                  exit when Main'Length = 0;
                  Ada_Mains.Increment_Last;
                  Ada_Mains.Table (Ada_Mains.Last) := new String'(Main);
               end;
            end loop;

         else
            Osint.Fail
              ("project ", Project_Name, " contains no source");
         end if;

      else
         Mains.Reset;

         loop
            declare
               Main : constant String := Mains.Next_Main;
            begin
               Name_Len := Main'Length;
               exit when Name_Len = 0;
               Name_Buffer (1 .. Name_Len) := Main;
               Canonical_Case_File_Name (Name_Buffer (1 .. Name_Len));
               Source_Name := Name_Find;

               if not Sources_Compiled.Get (Source_Name) then
                  Sources_Compiled.Set (Source_Name, True);

                  Source_Id := Data.First_Other_Source;

                  while Source_Id /= No_Other_Source loop
                     Source := Other_Sources.Table (Source_Id);
                     exit when Source.File_Name = Source_Name;
                     Source_Id := Source.Next;
                  end loop;

                  if Source_Id = No_Other_Source then
                     if Ada_Is_A_Language then
                        Ada_Mains.Increment_Last;
                        Ada_Mains.Table (Ada_Mains.Last) :=
                          new String'(Main);

                     else
                        Report_Error
                          (Main,
                           " is not a valid source of project ",
                           Project_Name);
                     end if;

                  else
                     Compile (Source_Id, Data, Dummy);
                  end if;
               end if;
            end;
         end loop;
      end if;

      if Ada_Mains.Last > 0 then

         --  Invoke gnatmake for all sources that are not of a non Ada language

         Last_Argument := 0;

         Add_Argument (Dash_u, True);

         for Index in 1 .. Ada_Mains.Last loop
            Add_Argument (Ada_Mains.Table (Index), True);
         end loop;

         Compile_Link_With_Gnatmake (Mains_Specified => False);
      end if;
   end Compile_Individual_Sources;

   --------------------------------
   -- Compile_Link_With_Gnatmake --
   --------------------------------

   procedure Compile_Link_With_Gnatmake (Mains_Specified : Boolean) is
      Data    : constant Project_Data := Projects.Table (Main_Project);
      Success : Boolean;

   begin
      --  Array Arguments may already contain some arguments, so we don't
      --  set Last_Argument to 0.

      --  Get the gnatmake to invoke

      Get_Compiler (Lang_Ada);

      --  Specify the project file

      Add_Argument (Dash_P, True);
      Add_Argument (Get_Name_String (Data.Path_Name), True);

      --  If Mains_Specified is True, find the mains in package Mains

      if Mains_Specified then
         Mains.Reset;

         loop
            declare
               Main : constant String := Mains.Next_Main;
            begin
               exit when Main'Length = 0;
               Add_Argument (Main, True);
            end;
         end loop;
      end if;

      --  Specify output file name, if any was specified on the command line

      if Output_File_Name /= null then
         Add_Argument (Dash_o, True);
         Add_Argument (Output_File_Name, True);
      end if;

      --  Transmit to gnatmake some switches

      --  -c

      if Compile_Only then
         Add_Argument (Dash_c, True);
      end if;

      --  -k

      if Keep_Going then
         Add_Argument (Dash_k, True);
      end if;

      --  -f

      if Force_Compilations then
         Add_Argument (Dash_f, True);
      end if;

      --  -v

      if Verbose_Mode then
         Add_Argument (Dash_v, True);
      end if;

      --  -q

      if Quiet_Output then
         Add_Argument (Dash_q, True);
      end if;

      --  -vP1 and -vP2

      case Current_Verbosity is
         when Default =>
            null;

         when Medium =>
            Add_Argument (Dash_vP1, True);

         when High =>
            Add_Argument (Dash_vP2, True);
      end case;

      --  If there are compiling options for Ada, transmit them to gnatmake

      if Comp_Opts.Last (Options (Lang_Ada)) /= 0 then
         Add_Argument (Dash_cargs, True);

         for Arg in 1 .. Comp_Opts.Last (Options (Lang_Ada)) loop
            Add_Argument (Options (Lang_Ada).Table (Arg), True);
         end loop;
      end if;

      if not Compile_Only then
         --  If there are linking options from the command line, transmit them
         --  to gnatmake.

         if Linker_Options.Last /= 0 then
            Add_Argument (Dash_largs, True);

            for Arg in 1 .. Linker_Options.Last loop
               Add_Argument (Linker_Options.Table (Arg), True);
            end loop;

         else
            Add_Argument (Dash_largs, Verbose_Mode);
         end if;

         --  Add the archives

         Add_Archives (For_Gnatmake => True);
      end if;

      --  And invoke gnatmake

      Display_Command
        (Compiler_Names (Lang_Ada).all, Compiler_Paths (Lang_Ada));

      Spawn
        (Compiler_Paths (Lang_Ada).all,
         Arguments (1 .. Last_Argument),
         Success);

      --  Report an error if call to gnatmake failed

      if not Success then
         Report_Error
           ("invocation of ", Compiler_Names (Lang_Ada).all, " failed");
      end if;

   end Compile_Link_With_Gnatmake;

   ---------------------
   -- Compile_Sources --
   ---------------------

   procedure Compile_Sources is
      Data         : Project_Data;
      Source_Id    : Other_Source_Id;
      Source       : Other_Source;

      Local_Errors : Boolean := False;
      --  Set to True when there is a compilation error. Used only when
      --  Keep_Going is True, to inhibit the building of the archive.

      Need_To_Compile : Boolean;
      --  Set to True when a source needs to be compiled/recompiled.

      Need_To_Rebuild_Archive : Boolean := Force_Compilations;
      --  True when the archive needs to be built/rebuilt unconditionally

   begin
      --  For each project file

      for Project in 1 .. Projects.Last loop
         Local_Errors := False;
         Data := Projects.Table (Project);

         --  Nothing to do when no sources of language other than Ada

         if (not Data.Virtual) and then Data.Sources_Present then

            --  If the imported directory switches are unknown, compute them

            if not Data.Include_Data_Set then
               Get_Imported_Directories (Project, Data);
               Data.Include_Data_Set := True;
               Projects.Table (Project) := Data;
            end if;

            Need_To_Rebuild_Archive := Force_Compilations;

            --  Compilation will occur in the object directory

            Change_Dir (Get_Name_String (Data.Object_Directory));

            Source_Id := Data.First_Other_Source;

            --  Process each source one by one

            while Source_Id /= No_Other_Source loop
               Source := Other_Sources.Table (Source_Id);
               Need_To_Compile := Force_Compilations;

               --  Check if compilation is needed

               if not Need_To_Compile then
                  Check_Compilation_Needed (Source, Need_To_Compile);
               end if;

               --  Proceed, if compilation is needed

               if Need_To_Compile then

                  --  If a source is compiled/recompiled, of course the
                  --  archive will need to be built/rebuilt.

                  Need_To_Rebuild_Archive := True;
                  Compile (Source_Id, Data, Local_Errors);
               end if;

               --  Next source, if any

               Source_Id := Source.Next;
            end loop;

            --  If there was no compilation error, build/rebuild the archive
            --  if necessary.

            if not Local_Errors then
               Build_Archive (Project, Need_To_Rebuild_Archive);
            end if;
         end if;
      end loop;
   end Compile_Sources;

   ---------------
   -- Copyright --
   ---------------

   procedure Copyright is
   begin
      --  Only output the Copyright notice once

      if not Copyright_Output then
         Copyright_Output := True;
         Write_Eol;
         Write_Str ("GPRMAKE ");
         Write_Str (Gnatvsn.Gnat_Version_String);
         Write_Str (" Copyright 2004 Free Software Foundation, Inc.");
         Write_Eol;
      end if;
   end Copyright;

   ------------------------------------
   -- Create_Archive_Dependency_File --
   ------------------------------------

   procedure Create_Archive_Dependency_File
     (Name         : String;
      First_Source : Other_Source_Id)
   is
      Source_Id : Other_Source_Id := First_Source;
      Source    : Other_Source;
      Dep_File  : Ada.Text_IO.File_Type;
      use Ada.Text_IO;

   begin
      Create (Dep_File, Out_File, Name);

      while Source_Id /= No_Other_Source loop
         Source := Other_Sources.Table (Source_Id);
         Put_Line (Dep_File, Get_Name_String (Source.Object_Name));
         Put_Line (Dep_File, String (Source.Object_TS));
         Source_Id := Source.Next;
      end loop;

      Close (Dep_File);

   exception
      when others =>
         if Is_Open (Dep_File) then
            Close (Dep_File);
         end if;
   end Create_Archive_Dependency_File;

   ---------------------
   -- Display_Command --
   ---------------------

   procedure Display_Command
     (Name  : String;
      Path  : String_Access;
      CPATH : String_Access := null)
   is
   begin
      --  Only display the command in Verbose Mode (-v) or when
      --  not in Quiet Output (no -q).

      if Verbose_Mode or (not Quiet_Output) then
         --  In Verbose Mode output the full path of the spawned process

         if Verbose_Mode then
            if CPATH /= null then
               Write_Str  ("CPATH = ");
               Write_Line (CPATH.all);
            end if;

            Write_Str (Path.all);

         else
            Write_Str (Name);
         end if;

         --  Display only the arguments for which the display flag is set
         --  (in Verbose Mode, the display flag is set for all arguments)

         for Arg in 1 .. Last_Argument loop
            if Arguments_Displayed (Arg) then
               Write_Char (' ');
               Write_Str (Arguments (Arg).all);
            end if;
         end loop;

         Write_Eol;
      end if;
   end Display_Command;

   ------------------
   -- Get_Compiler --
   ------------------

   procedure Get_Compiler (For_Language : Programming_Language) is
      Data : constant Project_Data := Projects.Table (Main_Project);

      Ide : constant Package_Id :=
        Value_Of (Name_Ide, In_Packages => Data.Decl.Packages);
      --  The id of the package IDE in the project file

      Compiler : constant Variable_Value :=
        Value_Of
          (Name                    => Lang_Name_Ids (For_Language),
           Index                   => 0,
           Attribute_Or_Array_Name => Name_Compiler_Command,
           In_Package              => Ide);
      --  The value of Compiler_Command ("language") in package IDE, if defined

   begin
      --  No need to do it again if the compiler is known for this language

      if Compiler_Names (For_Language) = null then

         --  If compiler command is not defined for this language in package
         --  IDE, use the default compiler for this language.

         if Compiler = Nil_Variable_Value then
            Compiler_Names (For_Language) :=
              Default_Compiler_Names (For_Language);

         else
            Compiler_Names (For_Language) :=
              new String'(Get_Name_String (Compiler.Value));
         end if;

         --  Check we have a GCC compiler (name ends with "gcc" or "g++")

         declare
            Comp_Name : constant String := Compiler_Names (For_Language).all;
            Last3     : String (1 .. 3);
         begin
            if Comp_Name'Length >= 3 then
               Last3 := Comp_Name (Comp_Name'Last - 2 .. Comp_Name'Last);
               Compiler_Is_Gcc (For_Language) :=
                 (Last3 = "gcc") or (Last3 = "g++");
            else
               Compiler_Is_Gcc (For_Language) := False;
            end if;
         end;

         --  Locate the compiler on the path

         Compiler_Paths (For_Language) :=
           Locate_Exec_On_Path (Compiler_Names (For_Language).all);

         --  Fail if compiler cannot be found

         if Compiler_Paths (For_Language) = null then
            if For_Language = Lang_Ada then
               Osint.Fail
                 ("unable to locate """,
                  Compiler_Names (For_Language).all,
                  """");

            else
               Osint.Fail
                 ("unable to locate " & Lang_Display_Names (For_Language).all,
                  " compiler """, Compiler_Names (For_Language).all & '"');
            end if;
         end if;
      end if;
   end Get_Compiler;

   ------------------------------
   -- Get_Imported_Directories --
   ------------------------------

   procedure Get_Imported_Directories
     (Project : Project_Id;
      Data    : in out Project_Data)
   is
      Imported_Projects : Project_List := Data.Imported_Projects;

      Path_Length : Natural := 0;
      Position    : Natural := 0;

      procedure Add (Source_Dirs : String_List_Id);
      --  Add a list of source directories

      procedure Recursive_Get_Dirs (Prj : Project_Id);
      --  Recursive procedure to get the source directories of this project
      --  file and of the project files it imports, in the correct order.

      ---------
      -- Add --
      ---------

      procedure Add (Source_Dirs : String_List_Id) is
         Element_Id : String_List_Id := Source_Dirs;
         Element    : String_Element;
         Add_Arg    : Boolean := True;
      begin
         --  Add each source directory path name, preceded by "-I" to
         --  Arguments.

         while Element_Id /= Nil_String loop
            Element := String_Elements.Table (Element_Id);

            if Element.Value /= No_Name then
               Get_Name_String (Element.Value);

               if Name_Len > 0 then
                  declare
                     Arg : constant String :=
                             "-I" & Name_Buffer (1 .. Name_Len);
                  begin
                     --  Check if directory is already in the list.
                     --  If it is, no need to put it again.

                     for Index in 1 .. Last_Argument loop
                        if Arguments (Index).all = Arg then
                           Add_Arg := False;
                           exit;
                        end if;
                     end loop;

                     if Add_Arg then
                        if Path_Length /= 0 then
                           Path_Length := Path_Length + 1;
                        end if;

                        Path_Length := Path_Length + Name_Len;

                        Add_Argument (Arg, True);
                     end if;
                  end;
               end if;
            end if;

            Element_Id := Element.Next;
         end loop;
      end Add;

      ------------------------
      -- Recursive_Get_Dirs --
      ------------------------

      procedure Recursive_Get_Dirs (Prj : Project_Id) is
         Data     : Project_Data;
         Imported : Project_List;

      begin
         --  Nothing to do if project is undefined

         if Prj /= No_Project then
            Data := Projects.Table (Prj);

            --  Nothing to do if project has already been processed

            if not Data.Seen then

               --  Mark the project as processed, to avoid multiple processing
               --  of the same project.

               Projects.Table (Prj).Seen := True;

               --  Add the source directories of this project

               if not Data.Virtual then
                  Add (Data.Source_Dirs);
               end if;

               Recursive_Get_Dirs (Data.Extends);

               Imported := Data.Imported_Projects;

               --  Call itself for all imported projects, if any

               while Imported /= Empty_Project_List loop
                  Recursive_Get_Dirs (Project_Lists.Table (Imported).Project);
                  Imported := Project_Lists.Table (Imported).Next;
               end loop;
            end if;
         end if;
      end Recursive_Get_Dirs;

   begin
      --  First, mark all project as not processed

      for J in 1 .. Projects.Last loop
         Projects.Table (J).Seen := False;
      end loop;

      --  Empty Arguments

      Last_Argument := 0;

      --  Process this project individually, project data are already known

      Projects.Table (Project).Seen := True;

      Add (Data.Source_Dirs);

      Recursive_Get_Dirs (Data.Extends);

      while Imported_Projects /= Empty_Project_List loop
         Recursive_Get_Dirs (Project_Lists.Table (Imported_Projects).Project);
         Imported_Projects := Project_Lists.Table (Imported_Projects).Next;
      end loop;

      Data.Imported_Directories_Switches :=
        new Argument_List'(Arguments (1 .. Last_Argument));

      --  Create the Include_Path, from the Arguments

      Data.Include_Path := new String (1 .. Path_Length);
      Data.Include_Path (1 .. Arguments (1)'Length - 2) :=
        Arguments (1)(Arguments (1)'First + 2 .. Arguments (1)'Last);
      Position := Arguments (1)'Length - 2;

      for Arg in 2 .. Last_Argument loop
         Position := Position + 1;
         Data.Include_Path (Position) := Path_Separator;
         Data.Include_Path
           (Position + 1 .. Position + Arguments (Arg)'Length - 2) :=
           Arguments (Arg)(Arguments (Arg)'First + 2 .. Arguments (Arg)'Last);
         Position := Position + Arguments (Arg)'Length - 2;
      end loop;

      Last_Argument := 0;
   end Get_Imported_Directories;

   -------------
   -- Gprmake --
   -------------

   procedure Gprmake is
   begin
      Initialize;

      if Verbose_Mode then
         Write_Eol;
         Write_Str ("Parsing Project File """);
         Write_Str (Project_File_Name.all);
         Write_Str (""".");
         Write_Eol;
      end if;

      --  Parse and process the project files for other languages
      --  (not for Ada).

      Prj.Pars.Parse
        (Project           => Main_Project,
         Project_File_Name => Project_File_Name.all,
         Packages_To_Check => Packages_To_Check,
         Process_Languages => Other_Languages);

      --  Fail if parsing/processing was unsuccessful

      if Main_Project = No_Project then
         Osint.Fail ("""", Project_File_Name.all, """ processing failed");
      end if;

      if Verbose_Mode then
         Write_Eol;
         Write_Str ("Parsing of Project File """);
         Write_Str (Project_File_Name.all);
         Write_Str (""" is finished.");
         Write_Eol;
      end if;

      --  If -f was specified, we will certainly need to link (except when
      --  -u or -c were specified, of course).

      Need_To_Relink := Force_Compilations;

      if Unique_Compile then
         if Mains.Number_Of_Mains = 0 then
            Osint.Fail
              ("No source specified to compile in 'unique compile' mode");

         else
            Compile_Individual_Sources;
            Report_Total_Errors ("compilation");
         end if;

      else
         --  First compile sources and build archives, if necessary

         Compile_Sources;

         --  When Keep_Going is True, if we had some errors, fail now,
         --  reporting the number of compilation errors.
         --  Do not attempt to link.

         Report_Total_Errors ("compilation");

         --  If -c was not specified, link the executables, if there are any.

         if not Compile_Only then
            Check_For_C_Plus_Plus;
            Link_Executables;
         end if;

         --  When Keep_Going is True, if we had some errors, fail, reporting
         --  the number of linking errors.

         Report_Total_Errors ("linking");
      end if;
   end Gprmake;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      --  Do some necessary package initializations

      Csets.Initialize;
      Namet.Initialize;
      Snames.Initialize;
      Prj.Initialize;
      Mains.Delete;

      --  Set Name_Ide and Name_Compiler_Command

      Name_Len := 0;
      Add_Str_To_Name_Buffer ("ide");
      Name_Ide := Name_Find;

      Name_Len := 0;
      Add_Str_To_Name_Buffer ("compiler_command");
      Name_Compiler_Command := Name_Find;

      --  Get the command line arguments

      Scan_Args : for Next_Arg in 1 .. Argument_Count loop
         Scan_Arg (Argument (Next_Arg));
      end loop Scan_Args;

      --  Fail if command line ended with "-P"

      if Project_File_Name_Expected then
         Osint.Fail ("project file name missing after -P");

      --  Or if it ended with "-o"

      elsif Output_File_Name_Expected then
         Osint.Fail ("output file name missing after -o");
      end if;

      --  If no project file was specified, display the usage and fail

      if Project_File_Name = null then
         Usage;
         Exit_Program (E_Success);
      end if;

      --  To be able of finding libgnat.a in MLib.Tgt, we need to have the
      --  default search dirs established in Osint.

      Osint.Add_Default_Search_Dirs;
   end Initialize;

   ----------------------
   -- Link_Executables --
   ----------------------

   procedure Link_Executables is
      Data : constant Project_Data := Projects.Table (Main_Project);

      Mains_Specified : constant Boolean := Mains.Number_Of_Mains /= 0;
      --  True if main sources were specified on the command line

      Object_Dir : constant String := Get_Name_String (Data.Object_Directory);
      --  Path of the object directory of the main project

      Source_Id : Other_Source_Id;
      Source    : Other_Source;
      Success   : Boolean;

      Linker_Name : String_Access;
      Linker_Path : String_Access;
      --  The linker name and path, when linking is not done by gnatlink

      Link_Done   : Boolean := False;
      --  Set to True when the linker is invoked directly (not through
      --  gnatmake) to be able to report if mains were up to date at the end
      --  of execution.

      procedure Add_C_Plus_Plus_Link_For_Gnatmake;
      --  Add the --LINK= switch for gnatlink, depending on the C++ compiler

      procedure Choose_C_Plus_Plus_Link_Process;
      --  If the C++ compiler is not g++, create the correct script to link

      ---------------------------------------
      -- Add_C_Plus_Plus_Link_For_Gnatmake --
      ---------------------------------------

      procedure Add_C_Plus_Plus_Link_For_Gnatmake is
      begin
         if Compiler_Is_Gcc (Lang_C_Plus_Plus) then
            Add_Argument
              ("--LINK=" & Compiler_Names (Lang_C_Plus_Plus).all,
               Verbose_Mode);

         else
            Add_Argument
              ("--LINK=" &
               Object_Dir & Directory_Separator &
               Cpp_Linker,
               Verbose_Mode);
         end if;
      end Add_C_Plus_Plus_Link_For_Gnatmake;

      -------------------------------------
      -- Choose_C_Plus_Plus_Link_Process --
      -------------------------------------

      procedure Choose_C_Plus_Plus_Link_Process is
      begin
         if Compiler_Names (Lang_C_Plus_Plus) = null then
            Get_Compiler (Lang_C_Plus_Plus);
         end if;

         if not Compiler_Is_Gcc (Lang_C_Plus_Plus) then
            Change_Dir (Object_Dir);

            declare
               procedure Set_Executable (Name : System.Address);
               pragma Import
                 (C, Set_Executable, "__gnat_set_executable");

               Name : constant String := Cpp_Linker & ASCII.NUL;

               File : Ada.Text_IO.File_Type;
               use Ada.Text_IO;

            begin
               Create (File, Out_File, Cpp_Linker);

               Put_Line (File, "#!/bin/sh");

               Put_Line (File, "LIBGCC=`gcc -print-libgcc-file-name`");
               Put_Line
                 (File,
                  Compiler_Names (Lang_C_Plus_Plus).all &
                  " $* ${LIBGCC}");

               Close (File);
               Set_Executable (Name (Name'First)'Address);
            end;
         end if;
      end Choose_C_Plus_Plus_Link_Process;

   begin
      --  If no mains specified, get mains from attribute Main, if it exists

      if not Mains_Specified then
         declare
            Element_Id : String_List_Id := Data.Mains;
            Element    : String_Element;

         begin
            while Element_Id /= Nil_String loop
               Element := String_Elements.Table (Element_Id);

               if Element.Value /= No_Name then
                  Mains.Add_Main (Get_Name_String (Element.Value));
               end if;

               Element_Id := Element.Next;
            end loop;
         end;
      end if;

      if Mains.Number_Of_Mains = 0 then
         --  If the attribute Main is an empty list or not specified,
         --  there is nothing to do.

         if Verbose_Mode then
            Write_Line ("No main to link");
         end if;
         return;
      end if;

      --  Check if -o was used for several mains

      if Output_File_Name /= null and then Mains.Number_Of_Mains > 1 then
         Osint.Fail ("cannot specify an executable name for several mains");
      end if;

      --  Check how we are going to do the link

      if not Data.Sources_Present then
         --  Only Ada sources in the main project, and even maybe not

         if not Data.Languages (Lang_Ada) then
            --  Fail if the main project has no source of any language

            Osint.Fail
              ("project """,
               Get_Name_String (Data.Name),
               """ has no sources, so no main can be linked");

         else
            --  Only Ada sources in the main project, call gnatmake directly

            Last_Argument := 0;

            --  Choose the correct linker if there is C++ code in other
            --  projects.

            if C_Plus_Plus_Is_Used then
               Choose_C_Plus_Plus_Link_Process;
               Add_Argument (Dash_largs, Verbose_Mode);
               Add_C_Plus_Plus_Link_For_Gnatmake;
               Add_Argument (Dash_margs, Verbose_Mode);
            end if;

            Compile_Link_With_Gnatmake (Mains_Specified);
         end if;

      else
         --  There are other language sources. First check if there are also
         --  sources in Ada.

         if Data.Languages (Lang_Ada) then
            --  There is a mix of Ada and other language sources in the main
            --  project. Any main that is not a source of the other languages
            --  will be deemed to be an Ada main.
            --
            --  Find the mains of the other languages and the Ada mains.

            Mains.Reset;
            Ada_Mains.Set_Last (0);
            Other_Mains.Set_Last (0);

            --  For each main

            loop
               declare
                  Main : constant String := Mains.Next_Main;
                  Main_Id : Name_Id;
               begin
                  exit when Main'Length = 0;

                  --  Get the main file name

                  Name_Len := 0;
                  Add_Str_To_Name_Buffer (Main);
                  Canonical_Case_File_Name (Name_Buffer (1 .. Name_Len));
                  Main_Id := Name_Find;
                  Source_Id := Data.First_Other_Source;

                  --  Check if it is a source of a language other than Ada

                  while Source_Id /= No_Other_Source loop
                     Source := Other_Sources.Table (Source_Id);
                     exit when Source.File_Name = Main_Id;
                     Source_Id := Source.Next;
                  end loop;

                  --  If it is not, put it in the list of Ada mains

                  if Source_Id = No_Other_Source then
                     Ada_Mains.Increment_Last;
                     Ada_Mains.Table (Ada_Mains.Last) := new String'(Main);

                  --  Otherwise, put it in the list of other mains

                  else
                     Other_Mains.Increment_Last;
                     Other_Mains.Table (Other_Mains.Last) := Source;
                  end if;
               end;
            end loop;

            --  If C++ is one of the other language, create the shell script
            --  to do the link.

            if C_Plus_Plus_Is_Used then
               Choose_C_Plus_Plus_Link_Process;
            end if;

            --  Call gnatmake with the necessary switches for each non-Ada
            --  main, if there are some.

            for Main in 1 .. Other_Mains.Last loop
               declare
                  Source : constant Other_Source := Other_Mains.Table (Main);
               begin
                  Last_Argument := 0;

                  --  Add -o if -o was specified

                  if Output_File_Name = null then
                     Add_Argument (Dash_o, True);
                     Add_Argument
                       (Get_Name_String
                          (Executable_Of
                             (Project  => Main_Project,
                              Main     => Other_Mains.Table (Main).File_Name,
                              Index    => 0,
                              Ada_Main => False)),
                        True);
                  end if;

                  --  Call gnatmake with the -B switch

                  Add_Argument (Dash_B, True);

                  --  Add to the linking options the object file of the source

                  Add_Argument (Dash_largs, Verbose_Mode);
                  Add_Argument
                    (Get_Name_String (Source.Object_Name), Verbose_Mode);

                  --  If C++ is one of the language, add the --LINK switch
                  --  to the linking switches.

                  if C_Plus_Plus_Is_Used then
                     Add_C_Plus_Plus_Link_For_Gnatmake;
                  end if;

                  --  Add -margs so that the following switches are for
                  --  gnatmake

                  Add_Argument (Dash_margs, Verbose_Mode);

                  --  And link with gnatmake

                  Compile_Link_With_Gnatmake (Mains_Specified => False);
               end;
            end loop;

            --  If there are also Ada mains, call gnatmake for all these mains

            if Ada_Mains.Last /= 0 then
               Last_Argument := 0;

               --  Put all the Ada mains as the first arguments

               for Main in 1 .. Ada_Mains.Last loop
                  Add_Argument (Ada_Mains.Table (Main).all, True);
               end loop;

               --  If C++ is one of the languages, add the --LINK switch to
               --  the linking switches.

               if Data.Languages (Lang_C_Plus_Plus) then
                  Add_Argument (Dash_largs, Verbose_Mode);
                  Add_C_Plus_Plus_Link_For_Gnatmake;
                  Add_Argument (Dash_margs, Verbose_Mode);
               end if;

               --  And link with gnatmake

               Compile_Link_With_Gnatmake (Mains_Specified => False);
            end if;

         else
            --  No Ada source in main project

            --  First, get the linker to invoke

            if Data.Languages (Lang_C_Plus_Plus) then
               Get_Compiler (Lang_C_Plus_Plus);
               Linker_Name := Compiler_Names (Lang_C_Plus_Plus);
               Linker_Path := Compiler_Paths (Lang_C_Plus_Plus);

            else
               Get_Compiler (Lang_C);
               Linker_Name := Compiler_Names (Lang_C);
               Linker_Path := Compiler_Paths (Lang_C);
            end if;

            Link_Done := False;

            Mains.Reset;

            --  Get each main, check if it is a source of the main project,
            --  and if it is, invoke the linker.

            loop
               declare
                  Main : constant String := Mains.Next_Main;
                  Main_Id : Name_Id;
               begin
                  exit when Main'Length = 0;

                  --  Get the file name of the main

                  Name_Len := 0;
                  Add_Str_To_Name_Buffer (Main);
                  Canonical_Case_File_Name (Name_Buffer (1 .. Name_Len));
                  Main_Id := Name_Find;
                  Source_Id := Data.First_Other_Source;

                  --  Check if it is a source of the main project file

                  while Source_Id /= No_Other_Source loop
                     Source := Other_Sources.Table (Source_Id);
                     exit when Source.File_Name = Main_Id;
                     Source_Id := Source.Next;
                  end loop;

                  --  Report an error if it is not

                  if Source_Id = No_Other_Source then
                     Report_Error
                       (Main, "is not a source of project ",
                        Get_Name_String (Data.Name));

                  else
                     declare
                        Executable_Name : constant String :=
                          Get_Name_String
                            (Executable_Of
                                 (Project  => Main_Project,
                                  Main     => Main_Id,
                                  Index    => 0,
                                  Ada_Main => False));
                        --  File name of the executable

                        Executable_Path : constant String :=
                                            Get_Name_String
                                              (Data.Exec_Directory) &
                                            Directory_Separator &
                                            Executable_Name;
                        --  Path name of the executable

                        Exec_Time_Stamp : Time_Stamp_Type;

                     begin
                        --  Now, check if the executable is up to date.
                        --  It is considered up to date if its time stamp is
                        --  not earlier that the time stamp of any archive.
                        --  Only do that if we don't know if we need to link.

                        if not Need_To_Relink then

                           --  Get the time stamp of the executable

                           Name_Len := 0;
                           Add_Str_To_Name_Buffer (Executable_Path);
                           Exec_Time_Stamp := File_Stamp (Name_Find);

                           if Verbose_Mode then
                              Write_Str  ("   Checking executable ");
                              Write_Line (Executable_Name);
                           end if;

                           --  If executable does not exist, we need to link

                           if Exec_Time_Stamp = Empty_Time_Stamp then
                              Need_To_Relink := True;

                              if Verbose_Mode then
                                 Write_Line ("      -> not found");
                              end if;

                           else
                              --  Otherwise, get the time stamps of each
                              --  archive. If one of them is found later than
                              --  the executable, we need to relink.

                              declare
                                 Prj_Data : Project_Data;

                              begin
                                 for Prj in 1 .. Projects.Last loop
                                    Prj_Data := Projects.Table (Prj);

                                    --  There is an archive only in project
                                    --  files with sources other than Ada
                                    --  sources.

                                    if Data.Sources_Present then
                                       declare
                                          Archive_Path : constant String :=
                                            Get_Name_String
                                              (Prj_Data.Object_Directory) &
                                          Directory_Separator &
                                          "lib" &
                                          Get_Name_String (Prj_Data.Name) &
                                          '.' & Archive_Ext;
                                          Archive_TS : Time_Stamp_Type;
                                       begin
                                          Name_Len := 0;
                                          Add_Str_To_Name_Buffer
                                            (Archive_Path);
                                          Archive_TS := File_Stamp (Name_Find);

                                          --  If the archive is later than the
                                          --  executable, we need to relink.

                                          if Archive_TS /=  Empty_Time_Stamp
                                            and then
                                              Exec_Time_Stamp < Archive_TS
                                          then
                                             Need_To_Relink := True;

                                             if Verbose_Mode then
                                                Write_Str ("      -> ");
                                                Write_Str (Archive_Path);
                                                Write_Str (" has time stamp ");
                                                Write_Str ("later than ");
                                                Write_Line ("executable");
                                             end if;

                                             exit;
                                          end if;
                                       end;
                                    end if;
                                 end loop;
                              end;
                           end if;

                           --  If Need_To_Relink is False, we are done

                           if Verbose_Mode and (not Need_To_Relink) then
                              Write_Line ("      -> up to date");
                           end if;

                        end if;

                        --  Prepare to link

                        if Need_To_Relink then
                           Link_Done := True;

                           Last_Argument := 0;

                           --  Specify the executable path name

                           Add_Argument (Dash_o, True);
                           Add_Argument
                             (Get_Name_String (Data.Exec_Directory) &
                              Directory_Separator &
                              Get_Name_String
                                (Executable_Of
                                   (Project  => Main_Project,
                                    Main     => Main_Id,
                                    Index    => 0,
                                    Ada_Main => False)),
                              True);

                           --  Specify the object file of the main source

                           Add_Argument
                             (Object_Dir & Directory_Separator &
                              Get_Name_String (Source.Object_Name),
                              True);

                           --  Add the switches specified in package Linker of
                           --  the main project.

                           Add_Switches
                             (Data      => Data,
                              Proc      => Linker,
                              Language  => Source.Language,
                              File_Name => Main_Id);

                           --  Add the switches specified in attribute
                           --  Linker_Options of packages Linker.

                           if Link_Options_Switches = null then
                              Link_Options_Switches :=
                                new Argument_List'
                                  (Linker_Options_Switches (Main_Project));
                           end if;

                           Add_Arguments (Link_Options_Switches.all, True);

                           --  Add the linking options specified on the
                           --  command line.

                           for Arg in 1 ..  Linker_Options.Last loop
                              Add_Argument (Linker_Options.Table (Arg), True);
                           end loop;

                           --  Add all the archives, in a correct order

                           Add_Archives (For_Gnatmake => False);

                           --  If there are shared libraries and the run path
                           --  option is supported, add the run path switch.

                           if Lib_Path.Last > 0 then
                              Add_Argument
                                (Path_Option.all &
                                 String (Lib_Path.Table (1 .. Lib_Path.Last)),
                                Verbose_Mode);
                           end if;

                           --  And invoke the linker

                           Display_Command (Linker_Name.all, Linker_Path);
                           Spawn
                             (Linker_Path.all,
                              Arguments (1 .. Last_Argument),
                              Success);

                           if not Success then
                              Report_Error ("could not link ", Main);
                           end if;
                        end if;
                     end;
                  end if;
               end;
            end loop;

            --  If no linking was done, report it, except in Quiet Output

            if (Verbose_Mode or (not Quiet_Output)) and (not Link_Done) then
               Osint.Write_Program_Name;

               if Mains.Number_Of_Mains = 1 then
                  --  If there is only one executable, report its name too

                  Write_Str (": """);
                  Mains.Reset;

                  declare
                     Main : constant String := Mains.Next_Main;
                     Main_Id : Name_Id;
                  begin
                     Name_Len := 0;
                     Add_Str_To_Name_Buffer (Main);
                     Main_Id := Name_Find;
                     Write_Str
                       (Get_Name_String
                          (Executable_Of
                             (Project  => Main_Project,
                              Main     => Main_Id,
                              Index    => 0,
                              Ada_Main => False)));
                     Write_Line (""" up to date");
                  end;

               else
                  Write_Line (": all executables up to date");
               end if;
            end if;
         end if;
      end if;
   end Link_Executables;

   ------------------
   -- Report_Error --
   ------------------

   procedure Report_Error
     (S1 : String;
      S2 : String := "";
      S3 : String := "")
   is
   begin
      --  If Keep_Going is True, output the error message, preceded by the
      --  error header.

      if Keep_Going then
         Total_Number_Of_Errors := Total_Number_Of_Errors + 1;
         Write_Str (Error_Header);
         Write_Str (S1);
         Write_Str (S2);
         Write_Str (S3);
         Write_Eol;

      else
         --  Otherwise, just fail

         Osint.Fail (S1, S2, S3);
      end if;
   end Report_Error;

   -------------------------
   -- Report_Total_Errors --
   -------------------------

   procedure Report_Total_Errors (Kind : String) is
   begin
      if Total_Number_Of_Errors /= 0 then
         if Total_Number_Of_Errors = 1 then
            Osint.Fail
              ("One ", Kind, " error");

         else
            Osint.Fail
              ("Total of" & Total_Number_Of_Errors'Img,
               ' ' & Kind & " errors");
         end if;
      end if;
   end Report_Total_Errors;

   --------------
   -- Scan_Arg --
   --------------

   procedure Scan_Arg (Arg : String) is
   begin
      pragma Assert (Arg'First = 1);

      if Arg'Length = 0 then
         return;
      end if;

      --  If preceding switch was -P, a project file name need to be specified,
      --  not a switch.

      if Project_File_Name_Expected then
         if Arg (1) = '-' then
            Osint.Fail ("project file name missing after -P");
         else
            Project_File_Name_Expected := False;
            Project_File_Name := new String'(Arg);
         end if;

      --  If preceding switch was -o, an executable name need to be specidied,
      --  not a switch.

      elsif Output_File_Name_Expected then
         if Arg (1) = '-' then
            Osint.Fail ("output file name missing after -o");
         else
            Output_File_Name_Expected := False;
            Output_File_Name := new String'(Arg);
         end if;

      --  Set the processor/language for the following switches

      --  -c???args: Compiler arguments

      elsif Arg'Length >= 6 and then
         Arg (Arg'First .. Arg'First + 1) = "-c" and then
      Arg (Arg'Last - 3 .. Arg'Last) = "args"

      then
         declare
            OK          : Boolean := False;
            Args_String : constant String :=
                            Arg (Arg'First + 2 .. Arg'Last - 4);

         begin
            for Lang in Programming_Language loop
               if Args_String = Lang_Args (Lang).all then
                  OK := True;
                  Current_Language := Lang;
                  exit;
               end if;
            end loop;

            if OK then
               Current_Processor := Compiler;

            else
               Osint.Fail ("illegal option """, Arg, """");
            end if;
         end;

      elsif Arg = "-largs" then
         Current_Processor := Linker;

      --  -gargs: gprmake

      elsif Arg = "-gargs" then
         Current_Processor := None;

      --  A special test is needed for the -o switch within a -largs since
      --  that is another way to specify the name of the final executable.

      elsif Current_Processor = Linker and then Arg = "-o" then
         Osint.Fail
           ("switch -o not allowed within a -largs. Use -o directly.");

      --  If current processor is not gprmake dirrectly, store the option in
      --  the appropriate table.

      elsif Current_Processor /= None then
         Add_Option (Arg);

      --  Switches start with '-'

      elsif Arg (1) = '-' then
         if Arg = "-c" then
            Compile_Only := True;

         elsif Arg = "-f" then
            Force_Compilations := True;

         elsif Arg = "-h" then
            Usage;

         elsif Arg = "-k" then
            Keep_Going := True;

         elsif Arg = "-o" then
            if Output_File_Name /= null then
               Osint.Fail ("cannot specify several -o switches");

            else
               Output_File_Name_Expected := True;
            end if;

         elsif Arg'Length >= 2 and then Arg (2) = 'P' then
            if Project_File_Name /= null then
               Osint.Fail ("cannot have several project files specified");

            elsif Arg'Length = 2 then
               Project_File_Name_Expected := True;

            else
               Project_File_Name := new String'(Arg (3 .. Arg'Last));
            end if;

         elsif Arg = "-q" then
            Quiet_Output := True;

         elsif Arg = "-u" then
            Unique_Compile := True;
            Compile_Only   := True;

         elsif Arg = "-v" then
            Verbose_Mode := True;

         elsif Arg'Length = 4 and then Arg (1 .. 3) = "-vP"
           and then Arg (4) in '0' .. '2'
         then
            case Arg (4) is
               when '0' =>
                  Current_Verbosity := Prj.Default;
               when '1' =>
                  Current_Verbosity := Prj.Medium;
               when '2' =>
                  Current_Verbosity := Prj.High;
               when others =>
                  null;
            end case;

         elsif Arg'Length >= 3 and then Arg (2) = 'X'
           and then Is_External_Assignment (Arg)
         then
            --  Is_External_Assignment has side effects
            --  when it returns True;

            null;

         else
            Osint.Fail ("illegal option """, Arg, """");
         end if;

      else
         --  Not a switch: must be a main

         Mains.Add_Main (Arg);
      end if;
   end Scan_Arg;

   -----------------
   -- Strip_CR_LF --
   -----------------

   function Strip_CR_LF (Text : String) return String is

      To  : String (1 .. Text'Length);
      Index_To : Natural := 0;

   begin
      for Index in Text'Range loop
         if (Text (Index) /= ASCII.CR) and then (Text (Index) /= ASCII.LF) then
            Index_To := Index_To + 1;
            To (Index_To) := Text (Index);
         end if;
      end loop;

      return To (1 .. Index_To);
   end Strip_CR_LF;

   -----------
   -- Usage --
   -----------

   procedure Usage is
   begin
      if not Usage_Output then
         Usage_Output := True;
         Copyright;

         Write_Str ("Usage: ");
         Osint.Write_Program_Name;
         Write_Str (" -P<project file> [opts]  [name] {");

         for Lang in Programming_Language loop
            Write_Str ("[-c");
            Write_Str (Lang_Args (Lang).all);
            Write_Str ("args opts] ");
         end loop;

         Write_Str ("[-largs opts] [-gargs opts]}");
         Write_Eol;
         Write_Eol;
         Write_Str ("  name is zero or more file names");
         Write_Eol;
         Write_Eol;

         --  GPRMAKE switches

         Write_Str ("gprmake switches:");
         Write_Eol;

         --  Line for -c

         Write_Str ("  -c       Compile only");
         Write_Eol;

         --  Line for -f

         Write_Str ("  -f       Force recompilations");
         Write_Eol;

         --  Line for -k

         Write_Str ("  -k       Keep going after compilation errors");
         Write_Eol;

         --  Line for -o

         Write_Str ("  -o name  Choose an alternate executable name");
         Write_Eol;

         --  Line for -P

         Write_Str ("  -Pproj   Use GNAT Project File proj");
         Write_Eol;

         --  Line for -q

         Write_Str ("  -q       Be quiet/terse");
         Write_Eol;

         --  Line for -u

         Write_Str
           ("  -u       Unique compilation. Only compile the given files");
         Write_Eol;

         --  Line for -v

         Write_Str ("  -v       Verbose output");
         Write_Eol;

         --  Line for -vPx

         Write_Str ("  -vPx     Specify verbosity when parsing Project Files");
         Write_Eol;

         --  Line for -X

         Write_Str ("  -Xnm=val Specify an external reference for " &
                    "Project Files");
         Write_Eol;
         Write_Eol;

         --  Lines for -c*args

         for Lang in Programming_Language loop
            declare
               Column : Positive := 13 + Lang_Args (Lang)'Length;
               --  "  -cargs opts" is the minimum and is 13 character long

            begin
               Write_Str ("  -c");
               Write_Str (Lang_Args (Lang).all);
               Write_Str ("args opts");

               loop
                  Write_Char (' ');
                  Column := Column + 1;
                  exit when Column >= 17;
               end loop;

               Write_Str ("opts are passed to the ");
               Write_Str (Lang_Display_Names (Lang).all);
               Write_Str (" compiler");
               Write_Eol;
            end;
         end loop;

         --  Line for -largs

         Write_Str ("  -largs opts    opts are passed to the linker");
         Write_Eol;

         --  Line for -gargs

         Write_Str ("  -gargs opts    opts directly interpreted by gprmake");
         Write_Eol;
         Write_Eol;

      end if;
   end Usage;

begin
   Makeutl.Do_Fail := Report_Error'Access;
end Makegpr;
