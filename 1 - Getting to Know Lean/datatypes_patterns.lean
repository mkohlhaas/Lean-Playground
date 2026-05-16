-- from previous chapters

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

/- ---------------------- -/
/- Datatypes and Patterns -/
/- ---------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=datatypes-and-patterns

-- product type       = collection of values (structure)
-- sum type           = allows choices
-- recursive datatype = datatype that can include instances of themselves (e.g. lists, trees, …)
-- inductive datatype = recursive sum type - consumed through pattern matching and recursive functions

-- Many of the built-in types are actually inductive datatypes in the standard library.

-- Bool has two constructors, false and true.
-- In the Lean standard library, true and false are re-exported from the Bool
-- namespace so that they can be written alone, rather than as Bool.true and
-- Bool.false.

inductive MyBool where
  | false : MyBool
  | true  : MyBool

#print Bool                                             

-- Peano: https://en.wikipedia.org/wiki/Peano_axioms
inductive MyNat where
  | zero 
  | succ (n : Nat)

#print Nat                                              

#check (Nat.succ)                                       

#eval Nat.succ Nat.zero                                 
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
#eval Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ Nat.zero
#eval Nat.zero.succ.succ.succ.succ                      
#eval (0 : Nat).succ.succ.succ.succ                     

/- ---------------- -/
/- Pattern Matching -/
/- ---------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=pattern-matching

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

def isZero' : Nat -> Bool
  | Nat.zero   => true
  | Nat.succ _ => false

def Nat.isZero := isZero'

def checkZero (n : Nat) : Bool :=
  n.isZero

#eval isZero 0                                          
#eval isZero 1                                          
#eval isZero 2                                          
#eval isZero 3                                          
#eval isZero 4                                          
#eval isZero 5                                          

#eval (0).isZero                                        
#eval (1).isZero                                        
#eval (2).isZero                                        
#eval (3).isZero                                        
#eval (4).isZero                                        
#eval (5).isZero                                        

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

def pred' : Nat -> Nat
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval pred 0                                            
#eval pred 1                                            
#eval pred 2                                            
#eval pred 3                                            
#eval pred 4                                            
#eval pred 5                                            
-- …
#eval pred 839                                          

#eval pred' 0                                           
#eval pred' 1                                           
#eval pred' 2                                           
#eval pred' 3                                           
#eval pred' 4                                           
#eval pred' 5                                           
-- …
#eval pred' 839                                         

-- pattern matching also works with structures
def depth (p : Point3D) : Float :=
  match p with
  | { x := _h,                                          
      y := _w,
      z :=  d } => d

def depth' : Point3D -> Float
  | {x, y, z} => z                                      

def depth'' : Point3D -> Float
  | {z, ..} => z                                      

def depth''' (p : Point3D) : Float :=
  Point3D.z p
  
def depth'''' (p : Point3D) : Float :=
  p.z
  
#eval depth     origin3D                                 
#eval depth'    origin3D                                 
#eval depth''   origin3D                                 
#eval depth'''  origin3D                                 
#eval depth'''' origin3D                                 

/- ------------------- -/
/- Recursive Functions -/
/- ------------------- -/

def fac : Nat -> Nat
  | Nat.zero   => 1
  | Nat.succ n => (n + 1) * fac n

def fac' : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fac' n

#eval fac  20                                            
#eval fac' 20                                            

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=recursive-functions

-- structural recursion
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not $ even k

def even' : Nat -> Bool
  | Nat.zero   => true
  | Nat.succ k => not $ even' k

#eval even  0
#eval even  1
#eval even  2
#eval even  3
#eval even  4
#eval even  5

#eval even' 0
#eval even' 1
#eval even' 2
#eval even' 3
#eval even' 4
#eval even' 5

def infiniteList : List Nat :=                         
  Nat.succ 0 :: infiniteList

-- Lean doesn't accept recursions which attempt to invoke itself on the original number
def evenLoops (n : Nat) : Bool :=                      
  match n with
  | Nat.zero   => true
  | Nat.succ k => not $ evenLoops n                         -- same `n` again

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ $ plus n k'

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => Nat.zero
  | Nat.succ k' => plus n $ times n k'

-- subtraction n−k takes n's predecessor k times
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => pred $ minus n k'

-- Requires a manual proof of termination. (Explored in the final chapter.)
def div (n : Nat) (k : Nat) : Nat :=                  
  if n < k
    then 0
    else Nat.succ $ div (n - k) k
