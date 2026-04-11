/- ====== -/
/- Monads -/
/- ====== -/

/- ========================== -/
/- One API, Many Applications -/
/- ========================== -/

-- this is a nitty-gritty presentation of manually nesting

/- ---------------------------------------- -/
/- Checking for none: Don't Repeat Yourself -/
/- ---------------------------------------- -/

-- index 0
def first (xs : List α) : Option α :=
  xs[0]? -- optional indexing notation

#eval first ([] : List Nat)                         
#eval first [1, 2, 3]                               

-- index 0, 2
def firstThird1 (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third => some (first, third)

#eval firstThird1 ([] : List Nat)                   
#eval firstThird1 [1, 2]                            
#eval firstThird1 [1, 2, 3]                         

-- index 0, 2, 4
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third =>
      match xs[4]? with
      | none       => none
      | some fifth => some (first, third, fifth)

#eval firstThirdFifth ([] : List Nat)               
#eval firstThirdFifth [1, 2]                        
#eval firstThirdFifth [1, 2, 3]                     
#eval firstThirdFifth [1, 2, 3, 4]                  
#eval firstThirdFifth [1, 2, 3, 4, 5]               

-- index 0, 2, 4, 6
def firstThirdFifthSeventh1 (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none       => none
  | some first =>
    match xs[2]? with
    | none       => none
    | some third =>
      match xs[4]? with
      | none       => none
      | some fifth =>
        match xs[6]? with
        | none         => none
        | some seventh => some (first, third, fifth, seventh)

#eval firstThirdFifthSeventh1 ([] : List Nat)       
#eval firstThirdFifthSeventh1 [1, 2]                
#eval firstThirdFifthSeventh1 [1, 2, 3]             
#eval firstThirdFifthSeventh1 [1, 2, 3, 4]          
#eval firstThirdFifthSeventh1 [1, 2, 3, 4, 5]       
#eval firstThirdFifthSeventh1 [1, 2, 3, 4, 5, 6]    
#eval firstThirdFifthSeventh1 [1, 2, 3, 4, 5, 6, 7] 
 
-- it is (often) good style to lift a repetitive segment into a helper function
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none   => none
  | some x => next x

-- index 0, 2
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

#eval firstThird ([] : List Nat)                    
#eval firstThird [1, 2]                             
#eval firstThird [1, 2, 3]                          

-- more parentheses and indents the bodies of functions
def firstThird2 (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))

#eval firstThird2 ([] : List Nat)                   
#eval firstThird2 [1, 2]                            
#eval firstThird2 [1, 2, 3]                         

/- --------------- -/
/- Infix Operators -/
/- --------------- -/

-- infix  (non-associative)    | parens must be explicitly given
-- infixl (left-associative)   | parens are stacked to the left
-- infixr (right-associative)  | parens are stacked to the right

-- + is left associative: w + x + y + z is equivalent to (((w + x) + y) + z)
#eval 1 + 2 + 3 + 4                                  
#eval (((1 + 2) + 3) + 4)                            

-- exponentiation operator ^ is right associative: w ^ x ^ y ^ z is equivalent to w ^ (x ^ (y ^ z)).
#eval 4 ^ 3 ^ 2                                      
#eval (4 ^ (3 ^ 2))                                  
#eval ((4 ^ 3) ^ 2)                                  

-- Comparison operators such as < are non-associative: x < y < z is a syntax error
#eval 1 < 2 < 3                                      

infixl:55 " ~~> " => andThen

-- The number following the colon declares the precedence of the new infix operator.

-- In ordinary mathematical notation, x + y * z is equivalent to x + (y * z) even
-- though both + and * are left associative.

-- index 0, 2
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

-- index 0, 2, 4, 6
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

#eval firstThirdFifthSeventh ([] : List Nat)         
#eval firstThirdFifthSeventh [1, 2]                  
#eval firstThirdFifthSeventh [1, 2, 3]               
#eval firstThirdFifthSeventh [1, 2, 3, 4]            
#eval firstThirdFifthSeventh [1, 2, 3, 4, 5]         
#eval firstThirdFifthSeventh [1, 2, 3, 4, 5, 6]      
#eval firstThirdFifthSeventh [1, 2, 3, 4, 5, 6, 7]   
 
/- -------------------------- -/
/- Propagating Error Messages -/
/- -------------------------- -/

inductive MyExcept (ε : Type) (α : Type) where
  | error : ε → MyExcept ε α
  | ok    : α → MyExcept ε α
deriving BEq, Hashable, Repr

#check Except                                        

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def ediblePlants : List String := ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 0                             
#eval get ediblePlants 1                             
#eval get ediblePlants 2                             
#eval get ediblePlants 3                             
#eval get ediblePlants 4                             

-- index 0
def firstE (xs : List α) : Except String α :=
  get xs 0

#eval firstE ([] : List Nat)                         
#eval firstE [1, 2, 3]                               

-- index 0, 2
def firstThirdE (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first  =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third  =>
      Except.ok (first, third)

#eval firstThirdE ([] : List Nat)                   
#eval firstThirdE [1, 2]                            
#eval firstThirdE [1, 2, 3]                         

-- index 0, 2, 4
def firstThirdFifthE (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first  =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third  =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth  =>
        Except.ok (first, third, fifth)

#eval firstThirdFifthE ([] : List Nat)              
#eval firstThirdFifthE [1, 2]                       
#eval firstThirdFifthE [1, 2, 3]                    
#eval firstThirdFifthE [1, 2, 3, 4]                 
#eval firstThirdFifthE [1, 2, 3, 4, 5]              

-- index 0, 2, 4, 6
def firstThirdFifthSeventhE (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first  =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third  =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth  =>
        match get xs 6 with
        | Except.error msg  => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)

#eval firstThirdFifthSeventhE ([] : List Nat)       
#eval firstThirdFifthSeventhE [1, 2]                
#eval firstThirdFifthSeventhE [1, 2, 3]             
#eval firstThirdFifthSeventhE [1, 2, 3, 4]          
#eval firstThirdFifthSeventhE [1, 2, 3, 4, 5]       
#eval firstThirdFifthSeventhE [1, 2, 3, 4, 5, 6]    
#eval firstThirdFifthSeventhE [1, 2, 3, 4, 5, 6, 7] 
 
def andThenE (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x      => next x

-- index 0, 2
def firstThirdE' (xs : List α) : Except String (α × α) :=
  andThenE (get xs 0) fun first  =>
  andThenE (get xs 2) fun third =>
  Except.ok (first, third)

-- helpers
def ok (x : α)     : Except ε α := Except.ok x
def fail (err : ε) : Except ε α := Except.error err

def getE (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none   => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

-- overwriting `~~>` from above
infixl:55 " ~~> " => andThenE

-- index 0, 2
def firstThirdE'' (xs : List α) : Except String (α × α) :=
  getE xs 0 ~~> fun first =>
  getE xs 2 ~~> fun third =>
  ok (first, third)

#eval firstThirdE'' ([] : List Nat)                  
#eval firstThirdE'' [1, 2]                           
#eval firstThirdE'' [1, 2, 3]                        
  
-- index 0, 2, 4, 6
def firstThirdFifthSeventhE'' (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)

#eval firstThirdFifthSeventhE'' ([] : List Nat)      
#eval firstThirdFifthSeventhE'' [1, 2]               
#eval firstThirdFifthSeventhE'' [1, 2, 3]            
#eval firstThirdFifthSeventhE'' [1, 2, 3, 4]         
#eval firstThirdFifthSeventhE'' [1, 2, 3, 4, 5]      
#eval firstThirdFifthSeventhE'' [1, 2, 3, 4, 5, 6]   
#eval firstThirdFifthSeventhE'' [1, 2, 3, 4, 5, 6, 7]
