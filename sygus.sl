(set-logic DTLIA)

(declare-datatype uhbNode_t
    (cons (nExists Bool) (nTime Int))
)

(declare-datatype microop_t
    (cons (valid Bool) (globalID Int) (coreID Int) (uopType Int) (virtAddr Int) (physAddr Int) (data Int) (Fetch uhbNode_t) (Execute uhbNode_t) (Writeback uhbNode_t))
)

(define-fun IsLoad ((i microop_t)) Bool (= (uopType i) 0))
(define-fun IsStore ((i microop_t)) Bool (= (uopType i) 1))
(define-fun IsFence ((i microop_t)) Bool (= (uopType i) 2))

(define-fun AddEdge ((src uhbNode_t) (dst uhbNode_t)) Bool
    (& (& (nExists src) (nExists dst)) (< (nTime src) (nTime dest)))
)

(define-fun ProgramOrder ((i microop_t) (j microop_t)) Bool
    (& (< (globalID i) (globalID j)) (= (coreID i) (coreID j)))
)


(synth-fun axiom ((i microop_t) (j microop_t)) Bool
    ;;Non terminals of the grammar
    ((I microop_t) (N uhbNode_t) (B Bool))
    ;;Define the grammar
    (
        (I microop_t (i j))
        (N uhbNode_t ((Fetch I) (Execute I) (Writeback I)))
        (B Bool (
            true false
            (IsLoad I)
            (IsStore I)
            (IsFence I)
            (AddEdge I)
            (ProgramOrder I I)
            (& B B)
            (| B B)
            (! B)
            (Imply B B)
        ))
    )
)

(constraint bool-expr)
(check-synth)