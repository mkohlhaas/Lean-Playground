-- from previous chapters

structure Point where
  x : Float
  y : Float
deriving Repr

/- ======================= -/
/- Additional Conveniences -/
/- ======================= -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=getting-to-know-conveniences

/- ----------------------------- -/
/- Automatic Implicit Parameters -/
/- ----------------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=automatic-implicit-parameters

def lengthExplicit {α : Type} (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ $ lengthExplicit ys

def lengthImplicit (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | _ :: ys => Nat.succ $ lengthImplicit ys

#eval lengthExplicit [1,2,3]                                      
#eval lengthImplicit [1,2,3]                                      

/- ---------------------------- -/
/- Pattern-Matching Definitions -/
/- ---------------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=pattern-matching-definitions

-- match expression can be written directly, without naming the argument at all
def lengthPatternMatching : List α → Nat
  | []      => 0
  | _ :: ys => Nat.succ $ lengthPatternMatching ys

#eval lengthPatternMatching [1,2,3]                               

-- with multiple arguments
def drop : Nat → List α → List α
  | Nat.zero, xs        => xs
  | _, []               => []
  | Nat.succ n, _ :: xs => drop n xs

#eval drop 2 [1,]                                                 
#eval drop 2 [1,2]                                                
#eval drop 2 [1,2,3]                                              
#eval drop 2 [1,2,3,4]                                            
#eval drop 2 [1,2,3,4,5]                                          

-- named arguments and patterns can be used in the same definition
def fromOption (default : α) : Option α → α
  | none   => default
  | some x => x

#eval fromOption 5 $ some 1                                       
#eval fromOption 5 none                                           

-- fromOption = getD from the standard library
-- using dot notation
#print Option.getD                                                
#eval none.getD "default"                                         
#eval (some "salmonberry").getD "default"                         

/- ----------------- -/
/- Local Definitions -/
/- ----------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=local-definitions

-- given a list of pairs returns a pair of lists
def unzipInefficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => (x :: (unzipInefficient xys).fst,                -- Oops, two recursive calls!!!
                      y :: (unzipInefficient xys).snd)

#eval unzipInefficient [(1, "a"), (2, "b"), (3, "c"), (4, "d")]  

-- only one recursive call with `let`
-- NOTE: To use `let` on a single line, separate the local definition from the body with a semicolon.
def unzipEfficient : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped : List α × List β := unzipEfficient xys
                     (x :: unzipped.fst, y :: unzipped.snd)

#eval unzipEfficient [(1, "a"), (2, "b"), (3, "c"), (4, "d")]    

-- Local definitions with `let` may also use pattern matching when one pattern is enough to match all cases.
def unzip : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let (xs, ys) : List α × List β := unzip xys      -- isn't possible with function arguments
                     (x :: xs, y :: ys)

#eval unzip [(1, "a"), (2, "b"), (3, "c"), (4, "d")]             

-- recursive `let` definitions must be explicitly indicated with `let rec`
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar      => soFar
    | y :: ys, soFar => helper ys $ y :: soFar
  helper xs []
 
#eval reverse [1,2,3,4,5]                                        

/- -------------- -/
/- Type Inference -/
/- -------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=type-inference

-- unzip' does not need type annotation
def unzip' : List (α × β) → List α × List β
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip' xys                      -- no type annotations
                     (x :: unzipped.fst, y :: unzipped.snd)

#eval unzip' [(1, "a"), (2, "b"), (3, "c"), (4, "d")]           

-- using an explicit match expression allows omitting the return type
def unzip'' (pairs : List (α × β)) :=
  match pairs with
  | []            => ([], [])
  | (x, y) :: xys => let unzipped := unzip'' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- omitting all types leads to confusing error messages 
def unzip''' pairs :=
  match pairs with
  | []            => ([], [])                                        -- a metavariable is an unknown part of a program, written ?m.XYZ in error messages
  | (x, y) :: xys => let unzipped := unzip''' xys
                     (x :: unzipped.fst, y :: unzipped.snd)

-- type annotations
def id1 (x : α) : α := x                                         -- identity function
def id2 (x : α)     := x                                         -- return type is infered 
def id3 x               := x                                    

/- --------------------- -/
/- Simultaneous Matching -/
/- --------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=simultaneous-matching

def dropSimultaneousMatching (n : Nat) (xs : List α) : List α :=
  match n, xs with -- simultaneous matching
  | Nat.zero, ys         => ys
  | _, []                => []
  | Nat.succ n , _ :: ys => dropSimultaneousMatching n ys

#eval dropSimultaneousMatching 2 [1,]                           
#eval dropSimultaneousMatching 2 [1,2]                          
#eval dropSimultaneousMatching 2 [1,2,3]                        
#eval dropSimultaneousMatching 2 [1,2,3,4]                      
#eval dropSimultaneousMatching 2 [1,2,3,4,5]                    

-- Lean tracks the connection between the expression being matched and the patterns,
-- and this information is used for purposes that include checking for termination
-- and propagating static type information.

-- termination checker revolts
def sameLengthPair (xs : List α) (ys : List β) : Bool :=  
  match (xs, ys) with                                                -- matching on a pair; not simultaneous matching! 
  | ([], [])             => true
  | (x :: xs', y :: ys') => sameLengthPair xs' ys'
  | _                    => false

-- matching both lists is also accepted
def sameLengthSimultaneousMatching (xs : List α) (ys : List β) : Bool :=
  match xs, ys with                                                  -- simultaneous matching
  | [], []             => true
  | _ :: xs', _ :: ys' => sameLengthSimultaneousMatching xs' ys'
  | _, _               => false

#eval sameLengthSimultaneousMatching [1,2,3]   [4,5,6]          
#eval sameLengthSimultaneousMatching [1,2,3]   [4,5,6,7]        
#eval sameLengthSimultaneousMatching [1,2,3,4] [5,6,7]          

/- ----------------------- -/
/- Natural Number Patterns -/
/- ----------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=natural-number-patterns

-- using literals instead of Nat.zero and Nat.succ
def evenLiterals : Nat → Bool
  | 0     => true
  | n + 1 => not $ evenLiterals n

#eval evenLiterals 0                                            
#eval evenLiterals 1                                            
#eval evenLiterals 2                                            
#eval evenLiterals 3                                            
#eval evenLiterals 4                                            
#eval evenLiterals 5                                            

def halveLiterals : Nat → Nat
  | Nat.zero              => 0
  | Nat.succ Nat.zero     => 0
  | Nat.succ $ Nat.succ n => halveLiterals n + 1

#eval halveLiterals 0                                           
#eval halveLiterals 1                                           
#eval halveLiterals 2                                           
#eval halveLiterals 3                                           
#eval halveLiterals 4                                           
#eval halveLiterals 5                                           
#eval halveLiterals 6                                           
#eval halveLiterals 7                                           

def halve : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => halve n + 1

#eval halve 0                                                   
#eval halve 1                                                   
#eval halve 2                                                   
#eval halve 3                                                   
#eval halve 4                                                   
#eval halve 5                                                   
#eval halve 6                                                   
#eval halve 7                                                   

-- the second argument to + should always be a literal Nat
def halveBad : Nat → Nat
  | 0     => 0
  | 1     => 0
  | 2 + n => halveBad n + 1                                     
  
/- ------------------- -/
/- Anonymous Functions -/
/- ------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=anonymous-functions

-- anonymous function
#check fun x => x + 1                                           

-- with type annotation
#check fun (x : Int) => x + 1                                   

-- with implicit type params
#check fun {α : Type} (x : α) => x                              

-- can be written with λ instead of `fun` (but not very common)
#check λx => x + 1                                              

-- special syntax
#check (· + 1)                                                  

-- anonymous function with pattern matching
#check fun                                                      
  | 0     => none
  | n + 1 => some n

-- function written as a function expression
def double := fun
  | 0     => 0
  | k + 1 => double k + 2

#check double                                                   

-- the same
def double' : Nat → Nat
  | 0     => 0
  | k + 1 => double k + 2

#check double'                                                  

-- centered dot `·`
#check fun x => x + 1                                           
#check (· + 1)                                                  

#check  (· + 5,  3) -- a function that returns a pair of numbers
#check ((· + 5), 3) -- a pair of a function and a number.       

#eval (· + 5, 3) 1                                              

#check (· , ·)                                                  
#eval  (· , ·) 1 2                                              

#eval (fun x => x + x) 5                                        

#eval (· * 2) 5                                                 
#eval (· + ·) 5 4                                               

/- ---------- -/
/- Namespaces -/
/- ---------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=namespaces

-- Each name in Lean occurs in a namespace, which is a collection of names. 
-- Namespaces may be nested.

-- names can be directly defined within a namespace
def Nat.double (x : Nat) : Nat := x + x

#eval (4).double                                                

namespace NewNamespace
def triple    (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 4 * x
end NewNamespace

#check (NewNamespace.triple)                                    
#check (NewNamespace.quadruple)                                 

-- open namespace prior to an expression
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple $ triple x

-- open namespace prior to a command
open NewNamespace in
#check (quadruple)                                              

open NewNamespace in
#eval   quadruple 5                                             

open NewNamespace in
#eval   triple 5                                                

#eval timesTwelve 5                                             

-- NOTE:
-- Namespaces may be opened for all following commands for the rest of the file.
-- To do this, omit the `in` from a top-level usage of open.

/- ------ -/
/- if let -/
/- ------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=if-let

-- When consuming values that have a sum type, it is often the case that only a single constructor is of interest.

inductive Inline : Type where
  | lineBreak
  | string    : String → Inline
  | emph      : Inline → Inline
  | strong    : Inline → Inline

def Inline.string1? (inl : Inline) : Option String :=
  match inl with
  | Inline.string s => some s
  | _               => none

-- an `if let` might be easier to read
def Inline.string2? (inl : Inline) : Option String :=
  if let Inline.string s := inl
    then some s
    else none

/- ------------------------------ -/
/- Positional Structure Arguments -/
/- ------------------------------ -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=positional-structure-arguments

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

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=string-interpolation

-- `s!` triggers string interpolation: expressions contained in curly braces inside the string are replaced with their values.

#eval s!"three fives is {NewNamespace.triple 5}"              

-- a function cannot be turned into a string
#check s!"three fives is {NewNamespace.triple}"               
