( set-logic BV )

 (synth-fun   p_0_c1  () Bool ) 
 (synth-fun   p_0_c2  () Bool ) 

 (synth-fun   q_0_e1  () Bool ) 
 (synth-fun   q_0_e2  () Bool ) 
 (synth-fun   q_0_e3  () Bool ) 
 (synth-fun   q_1_e1  () Bool ) 
 (synth-fun   q_1_e2  () Bool ) 
 (synth-fun   q_1_e3  () Bool ) 

 (synth-fun   w_c1   () Bool) 
 (synth-fun   w_c2   () Bool) 
 (synth-fun   w_e1   () Bool) 
 (synth-fun   w_e2   () Bool) 
 (synth-fun   w_e3   () Bool) 
(define-fun cdt (( c1 Bool) ( c2 Bool)( e1 Bool) ( e2 Bool) ( e3 Bool)) Bool 
 true
)

 (declare-const   u_c1   Bool) 
 (declare-const   u_c2   Bool) 
 (declare-const   u_e1   Bool) 
 (declare-const   u_e2   Bool) 
 (declare-const   u_e3   Bool) 
(define-fun selectme (( value_0 Bool) ( value_1 Bool) ( p_i_0 Bool) ( p_i_1 Bool)) Bool
(ite  p_i_0 value_0
(ite  p_i_1 value_1
false ))
)


(define-fun eval (( c1 Bool) ( c2 Bool) ( e1 Bool) ( e2 Bool) ( e3 Bool)( p_0_c1 Bool) ( p_0_c2 Bool)) Bool
(ite
(selectme  c1 c2 p_0_c1 p_0_c2 )

(and 
(=> (not e1 )
(and (not q_1_e1 )
(or
 (and      (selectme  true  false  p_0_c1  p_0_c2 )    (not   true  )) 
 (and      (selectme  false  false  p_0_c1  p_0_c2 )    (not   true  )) 
)
)
)
(=> (not e2 )
(and (not q_1_e2 )
(or
 (and      (selectme  true  false  p_0_c1  p_0_c2 )    (not   true  )) 
 (and      (selectme  false  false  p_0_c1  p_0_c2 )    (not   false  )) 
)
)
)
(=> (not e3 )
(and (not q_1_e3 )
(or
 (and      (selectme  true  false  p_0_c1  p_0_c2 )    (not   false  )) 
 (and      (selectme  false  false  p_0_c1  p_0_c2 )    (not   true  )) 
)
)
)
)

(and 
(=> (not e1 )
(and (not q_0_e1 )
(or
 (and     (not    (selectme  true  false  p_0_c1  p_0_c2 )   )   (not   true  )) 
 (and     (not    (selectme  false  false  p_0_c1  p_0_c2 )   )   (not   true  )) 
)
)
)
(=> (not e2 )
(and (not q_0_e2 )
(or
 (and     (not    (selectme  true  false  p_0_c1  p_0_c2 )   )   (not   true  )) 
 (and     (not    (selectme  false  false  p_0_c1  p_0_c2 )   )   (not   false  )) 
)
)
)
(=> (not e3 )
(and (not q_0_e3 )
(or
 (and     (not    (selectme  true  false  p_0_c1  p_0_c2 )   )   (not   false  )) 
 (and     (not    (selectme  false  false  p_0_c1  p_0_c2 )   )   (not   true  )) 
)
)
)
)
)

)

(constraint 
(and
(or p_0_c1 p_0_c2)
(=> p_0_c1 (and ( not p_0_c2)))
(=> p_0_c2 (and ( not p_0_c1)))
( => ( eval u_c1 u_c2 u_e1 u_e2 u_e3 p_0_c1 p_0_c2) (cdt u_c1 u_c2 u_e1 u_e2 u_e3))
(cdt w_c1 w_c2 w_e1 w_e2 w_e3)
(not (eval w_c1 w_c2 w_e1 w_e2 w_e3 p_0_c1 p_0_c2 ))
))
(check-synth)