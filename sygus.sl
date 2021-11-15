(set-logic DTLIA)

(declare-datatype uhbNode_t
    ((cons (nExists Bool) (nTime Int)))
)

(declare-datatype microop_t
    ((cons (valid Bool) (globalID Int) (coreID Int) (uopType Int) (virtAddr Int) (physAddr Int) (data Int) (Fetch uhbNode_t) (Execute uhbNode_t) (Writeback uhbNode_t)))
)

(define-fun IsLoad ((i microop_t)) Bool (= (uopType i) 0))
(define-fun IsStore ((i microop_t)) Bool (= (uopType i) 1))
(define-fun IsFence ((i microop_t)) Bool (= (uopType i) 2))

(define-fun AddEdge ((src uhbNode_t) (dst uhbNode_t)) Bool
    (and (and (nExists src) (nExists dst)) (< (nTime src) (nTime dst)))
)
(define-fun EdgeExists ((src uhbNode_t) (dst uhbNode_t)) Bool
    (and (and (nExists src) (nExists dst)) (< (nTime src) (nTime dst)))
)

(define-fun NodeExists ((n uhbNode_t)) Bool
    (nExists n)
)

(define-fun ProgramOrder ((i microop_t) (j microop_t)) Bool
    (and (< (globalID i) (globalID j)) (= (coreID i) (coreID j)))
)
(define-fun SameCore ((i microop_t) (j microop_t)) Bool
    (= (coreID i) (coreID j))
)
(define-fun SamePhysicalAddress ((i microop_t) (j microop_t)) Bool
    (= (physAddr i) (physAddr j))
)
(define-fun SameData ((i microop_t) (j microop_t)) Bool
    (= (data i) (data j))
)
(define-fun DataFromInitialStateAtPA ((i microop_t)) Bool (= (data i) 0))
(define-fun SameMicroop ((i microop_t) (j microop_t)) Bool
    (= (globalID i) (globalID j))
)



(synth-fun axiom ((i microop_t) (j microop_t)) Bool
    ;;Non terminals of the grammar
    ((B Bool) (I microop_t) (N uhbNode_t) )
    ;;Define the grammar
    (
        (B Bool (
            (IsLoad I)
            (IsStore I)
            (IsFence I)
            (AddEdge N N)
            (EdgeExists N N)
            (NodeExists N)
            (ProgramOrder I I)
            (SameCore I I)
            (SamePhysicalAddress I I)
            (DataFromInitialStateAtPA I)
            (SameMicroop I I)
            (and B B)
            (or B B)
            (not B)
            (=> B B)
        ))
        (I microop_t (i j))
        (N uhbNode_t ((Fetch I) (Execute I) (Writeback I)))
    )
)

(declare-var i microop_t)
(declare-var j microop_t)

(constraint (= (ProgramOrder i j) (axiom i j)))
(check-synth)