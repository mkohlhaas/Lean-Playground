/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

/- ----------------------------- -/
/- Automatic Implicit Parameters -/
/- ----------------------------- -/

def lengthExplicit {α : Type} (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (lengthExplicit ys)

def lengthImplicit (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ (lengthImplicit ys)
  
/- ---------------------------- -/
/- Pattern-Matching Definitions -/
/- ---------------------------- -/

-- match expression can be written directly, without naming the argument at all
def lengthPatternMatching : List α → Nat
  | []      => 0
  | _ :: ys => Nat.succ (lengthPatternMatching ys)

-- with multiple arguments
def drop : Nat → List α → List α
  | Nat.zero, xs        => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

-- named arguments and patterns can be used in the same definition
def fromOption (default : α) : Option α → α
  | none   => default
  | some x => x

-- fromOption = getD from the standard library
-- using dot notation
#eval none.getD "default"                                         
#eval (some "salmonberry").getD "default"                         

/- ----------------- -/
/- Local Definitions -/
/- ----------------- -/

-- given a list of pairs returns a pair of lists
def unzipInefficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => (x :: (unzipInefficient xys).fst, y :: (unzipInefficient xys).snd) /- Oops, two recursive calls!!! -/

-- only one recursive call with `let`
-- NOTE: To use `let` on a single line, separate the local definition from the body with a semicolon.
def unzipEfficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped : List α × List β := unzipEfficient xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- Local definitions with `let` may also use pattern matching when one pattern is enough to match all cases.
def unzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let (xs, ys) : List α × List β := unzip xys
                     (x :: xs, y :: ys)

-- recursive `let` definitions must be explicitly indicated with `let rec`
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar      => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

/- -------------- -/
/- Type Inference -/
/- -------------- -/

-- unzip' does not need type annotation
def unzip' : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- using an explicit match expression allows omitting the return type
def unzip'' (pairs : List (α × β)) :=
  match pairs with
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip'' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- omitting all types leads to confusing error messages 
def unzip''' pairs :=
  match pairs with
  | []            => ([], []) -- a metavariable is an unknown part of a program, written ?m.XYZ in error messages
  | (x, y) :: xys => let unzipped := unzip''' xys
                     (x :: unzipped.fst, y :: unzipped.snd)


-- type annotations
def id1 (x : α) : α := x -- identity function
def id2 (x : α)     := x -- return type is infered 
def id3 x           := x                                          

/- --------------------- -/
/- Simultaneous Matching -/
/- --------------------- -/

def dropSimultaneousMatching (n : Nat) (xs : List α) : List α :=
  match n, xs with -- simultaneous matching
  | Nat.zero, ys         => ys
  | _, []                => []
  | Nat.succ n , _ :: ys => dropSimultaneousMatching n ys

-- Lean tracks the connection between the expression being matched and the patterns,
-- and this information is used for purposes that include checking for termination
-- and propagating static type information.

-- termination checker revolts
def sameLengthPair (xs : List α) (ys : List β) : Bool :=          
  match (xs, ys) with -- simultaneous matching is not matching on a pair
  | ([], [])             => true
  | (x :: xs', y :: ys') => sameLengthPair xs' ys'
  | _                    => false

-- matching both lists is also accepted
def sameLengthSimultaneousMatching (xs : List α) (ys : List β) : Bool :=
  match xs, ys with -- simultaneous matching
  | [], []             => true
  | _ :: xs', _ :: ys' => sameLengthSimultaneousMatching xs' ys'
  | _, _               => false

/- ----------------------- -/
/- Natural Number Patterns -/
/- ----------------------- -/

-- using literals instead of Nat.zero, Nat.succ. See even above
def evenLiterals : Nat → Bool
  | 0     => true
  | n + 1 => not $ evenLiterals n

def halveLiterals : Nat → Nat
  | Nat.zero              => 0
  | Nat.succ Nat.zero     => 0
  | Nat.succ (Nat.succ n) => halveLiterals n + 1

def halve : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => halve n + 1

-- the second argument to + should always be a literal Nat
def halveBad : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2 + n => halveBad n + 1                                         
  
/- ------------------- -/
/- Anonymous Functions -/
/- ------------------- -/

-- anonymous function
#check fun x => x + 1                                               

-- with type annotation
#check fun (x : Int) => x + 1                                       

-- with implicit type params
#check fun {α : Type} (x : α) => x                                  

-- can be written with λ instead of `fun` (but not very common)
#check λ x => x + 1                                                 

-- anonymous function with pattern matching
#check fun                                                          
  | 0     => none
  | n + 1 => some n

-- function written as a function expression
def double : Nat → Nat := fun
  | 0     => 0
  | k + 1 => double k + 2

-- the same
def double' : Nat → Nat
  | 0     => 0
  | k + 1 => double k + 2

-- centered dot `·`
#check fun x => x + 1                                               
#check (· + 1)                                                      

#check (· + 5, 3)   -- a function that returns a pair of numbers    
#check ((· + 5), 3) -- a pair of a function and a number.           

#eval (· , ·) 1 2                                                   

#eval (fun x => x + x) 5                                            

#eval (· * 2) 5                                                     

/- ---------- -/
/- Namespaces -/
/- ---------- -/

-- Each name in Lean occurs in a namespace, which is a collection of names. 
-- Namespaces may be nested.

-- names can be directly defined within a namespace
def Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double                                              

namespace NewNamespace
def triple    (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 4 * x
end NewNamespace

#check (NewNamespace.triple)                                        
#check (NewNamespace.quadruple)                                     

-- open namespace prior to an expression
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

-- open namespace prior to a command
open NewNamespace in
#check (quadruple)                                                  

-- NOTE:
-- Namespaces may be opened for all following commands for the rest of the file.
-- To do this, omit the `in` from a top-level usage of open.

/- ------ -/
/- if let -/
/- ------ -/

-- When consuming values that have a sum type, it is often the case that only a single constructor is of interest.

inductive Inline : Type where
  | lineBreak
  | string    : String → Inline
  | emph      : Inline → Inline
  | strong    : Inline → Inline

def Inline.string1? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _               => none

-- an `if let` might be easier to read
def Inline.string2? (inline : Inline) : Option String :=
  if let Inline.string s := inline
    then some s
    else none

/- ------------------------------ -/
/- Positional Structure Arguments -/
/- ------------------------------ -/

-- Constructing Structures:

-- 1. Constructor
#eval Point.mk 1 2                                                

-- 2. Brace Notation
#eval ({ x := 1, y := 2 } : Point)                                
#eval  { x := 1, y := 2   : Point }                               

-- 3. Positional Structure Arguments
-- NOTE: Be careful! Even though they look like the less-than sign < and greater-than sign >, these brackets are different.
-- They can be input using \< and \>, respectively.
#eval (⟨1, 2⟩ : Point)                                            

/- -------------------- -/
/- String Interpolation -/
/- -------------------- -/

-- `s!` triggers string interpolation: expressions contained in curly braces inside the string are replaced with their values.

#eval s!"three fives is {NewNamespace.triple 5}"                  

-- a function cannot be turned into a string
#check s!"three fives is {NewNamespace.triple}"                   
