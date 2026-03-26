- File Order
  -  1 Hello.lean
  -  2 Hello.sh
  -  3 HelloName.lean
  -  4 HelloName.sh
  -  5 countdown.lean
  -  6 countdown.sh
  -  7 greetingExercise.lean
  -  8 greetingExercise.sh
  -  9 $ lake new greeting -> greeting/
  - 10 $ lake new feline   -> feline/
  - 11 nestedActions.lean
  - 12 flexibleLayouts.lean
  - 13 interlude.lean

- Typical lake commands
  - $ lake help
  - $ lake help new
  - $ lake help exe
  - $ lake new
  - $ lake init
  - $ lake build
  - $ lake exe

- The module name hierarchy is decoupled from the namespace hierarchy.
  - In Lean, modules are units of code distribution, while namespaces are units of code organization.
  - That is, names defined in the module Greeting.Smile are not automatically in a corresponding namespace Greeting.Smile.
  - In particular, happy is in the Expression namespace.
  - Modules may place names into any namespace they like, and the code that imports them may open the namespace or not.
  - import is used to make the contents of a source file available, while open makes names from a namespace available in the current context without prefixes.


- In Lean, `main` can have one of three types:
  - main : IO Unit                  is used for simple programs that cannot read their command-line arguments and always return exit code 0
  - main : IO UInt32                is used for programs without arguments that may signal success or failure
  - main : List String → IO UInt32  is used for programs that take command-line arguments and signal success or failure


- A do expression contains a sequence of statements, which may be:
  -   · expressions that represent IO actions
  -   · ordinary local definitions with let and := where the defined name refers to the value of the provided expression
  -   · local definitions with let and ← where the defined name refers to the result of executing the value of the provided expression

- Furthermore, if and match expressions that occur immediately under a do are implicitly considered to have their own do in each branch. Inside of a do expression, nested actions are expressions with a left arrow immediately under parentheses. The Lean compiler implicitly lifts them to the nearest enclosing do, which may be implicitly part of a branch of a match or if expression, and gives them a unique name. This unique name then replaces the origin site of the nested action.
