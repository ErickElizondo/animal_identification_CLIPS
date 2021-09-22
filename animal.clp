;;;======================================================
;;;   Animal Identification Expert System
;;;
;;;     A simple expert system which attempts to identify
;;;     an animal based on its characteristics.
;;;     The knowledge base in this example is a 
;;;     collection of facts which represent backward
;;;     chaining rules. CLIPS forward chaining rules are
;;;     then used to simulate a backward chaining inference
;;;     engine.
;;;
;;;     CLIPS Version 6.4 Example
;;; 
;;;     To execute, merely load, reset, and run.
;;;     Answer questions yes or no.
;;;======================================================

(defmodule MAIN (export ?ALL)) 

(defmodule VALIDATE (import MAIN ?ALL))

(defmodule CHAIN (import MAIN ?ALL))

(defmodule ASK (import MAIN ?ALL))

;;;*************************
;;;* DEFGLOBAL DEFINITIONS *
;;;*************************

(defglobal MAIN
   ?*rule-index* = 1
   ?*validate* = TRUE)

;;;***************************
;;;* DEFFUNCTION DEFINITIONS *
;;;***************************

(deffunction generate-rule-name ()
   (bind ?name (sym-cat rule- ?*rule-index*))
   (bind ?*rule-index* (+ ?*rule-index* 1))
   (return ?name))

;;;***************************
;;;* DEFTEMPLATE DEFINITIONS *
;;;***************************

(deftemplate MAIN::rule 
   (slot name (default-dynamic (generate-rule-name)))
   (slot validate (default no))
   (multislot if)
   (multislot then)
   (multislot processed))
   
(deftemplate MAIN::question
   (multislot valid-answers)
   (slot variable)
   (slot query))

(deftemplate MAIN::answer
   (slot variable)
   (slot prefix (default ""))
   (slot postfix (default "")))
   
(deftemplate MAIN::goal
   (slot variable))
   
(deftemplate MAIN::variable
   (slot name)
   (slot value))
   
(deftemplate MAIN::activity)

(deftemplate MAIN::legalanswers
   (multislot values))
   
;;;**************************
;;;* INFERENCE ENGINE RULES *
;;;**************************

(defrule MAIN::startup
   =>
   (if ?*validate*
      then
      (focus VALIDATE CHAIN ASK)
      else
      (focus CHAIN ASK)))
   
(defrule MAIN::continue
   (declare (salience -10))
   ?f <- (activity)
   =>
   (retract ?f)
   (focus CHAIN ASK))
   
(defrule MAIN::goal-satified ""
   (goal (variable ?goal))
   (variable (name ?goal) (value ?value))
   (answer (prefix ?prefix) (postfix ?postfix) (variable ?goal))
   =>
   (println ?prefix ?value ?postfix))

;;; ##################
;;; CHAIN MODULE RULES 
;;; ##################

(defrule CHAIN::propagate-goal ""
   (logical (goal (variable ?goal))
            (rule (if ?variable $?)
                  (then ?goal ? ?value)))
   =>
   (assert (goal (variable ?variable))))

(defrule CHAIN::modify-rule-match-is ""
   (variable (name ?variable) (value ?value))
   ?f <- (rule (if ?variable is ?value and $?rest)
               (processed $?p))
   =>
   (modify ?f (if ?rest)
              (processed ?p ?variable is ?value and)))

(defrule CHAIN::rule-satisfied-is ""
   (variable (name ?variable) (value ?value))
   ?f <- (rule (if ?variable is ?value)
               (then ?goal ? ?goal-value)
               (processed $?p))
   =>
   (modify ?f (if) 
              (processed ?p ?variable is ?value #)))
              
(defrule CHAIN::apply-rule ""
   (logical (rule (if)
                  (then ?goal ? ?goal-value)))
   =>
   (assert (variable (name ?goal) (value ?goal-value))))

;;; ################
;;; ASK MODULE RULES 
;;; ################

(defrule ASK::ask-question-no-legalvalues ""
   (not (legalanswers))
   ?f1 <- (goal (variable ?variable))
   (question (variable ?variable) (query ?text))
   (not (variable (name ?variable)))
   =>
   (assert (activity))
   (retract ?f1)
   (print ?text " ")
   (assert (variable (name ?variable) (value (read)))))

(defrule ASK::ask-question-legalvalues ""
   (legalanswers (values $?answers))
   ?f1 <- (goal (variable ?variable))
   (question (variable ?variable) (query ?text))
   (not (variable (name ?variable)))
   =>
   (assert (activity))
   (retract ?f1)
   (print ?text " ")
   (print ?answers " ")
   (bind ?reply (read))
   (if (lexemep ?reply)
      then
      (bind ?reply (lowcase ?reply)))
   (if (member$ ?reply ?answers) 
     then (assert (variable (name ?variable) (value ?reply)))
     else (assert (goal (variable ?variable)))))

;;; #####################
;;; VALIDATE MODULE RULES 
;;; #####################
      
(defrule VALIDATE::copy-rule
   (declare (salience 10))
   ?f <- (rule (validate no))
   =>
   (duplicate ?f (validate yes))
   (modify ?f (validate done)))

(defrule VALIDATE::next-condition
   (declare (salience -10))
   ?f <- (rule (name ?name) (validate yes)
               (if ?a ?c ?v and $?rest))
   =>
   (modify ?f (if ?rest)))
   
(defrule VALIDATE::validation-complete
   (declare (salience -10))
   ?f <- (rule (validate yes) (if ? ? ?))
   =>
   (retract ?f))

;;; *******************
;;; Validation - Syntax
;;; *******************

(defrule VALIDATE::and-connector
   ?f <- (rule (name ?name) (validate yes)
               (if ?a ?c ?v ?connector&~and $?))
   =>
   (retract ?f)
   (println "In rule " ?name ", if conditions must be connected using and:" crlf
            "   " ?a " " ?c " " ?v " *" ?connector "*"))

(defrule VALIDATE::and-requires-additional-condition
   ?f <- (rule (name ?name) (validate yes)
               (if ?a ?c ?v and))
   =>
   (retract ?f)
   (println "In rule " ?name ", an additional condition should follow the final and:" crlf
            "   " ?a " " ?c " " ?v " and <missing condition>"))
               
(defrule VALIDATE::incorrect-number-of-then-terms          
   ?f <- (rule (name ?name) (validate yes)
               (then $?terms&:(<> (length$ ?terms) 3)))
   =>
   (retract ?f)
   (println "In rule " ?name ", then portion should be of the form <variable> is <value>:" crlf
            "   " (implode$ ?terms)))

(defrule VALIDATE::incorrect-number-of-if-terms          
   ?f <- (rule (name ?name) (validate yes)
               (if $?terms&:(< (length$ ?terms) 3)))
   =>
   (retract ?f)
   (println "In rule " ?name ", if portion contains an incomplete condition:" crlf
            "   " (implode$ ?terms)))

(defrule VALIDATE::incorrect-then-term-syntax          
   ?f <- (rule (name ?name) (validate yes)
               (then ?a ?c&~is ?v))
   =>
   (retract ?f)
   (println "In rule " ?name ", then portion should be of the form <variable> is <value>:" crlf
            "   " ?a " " ?c " " ?v " "))

(defrule VALIDATE::incorrect-if-term-syntax          
   ?f <- (rule (name ?name) (validate yes)
               (if ?a ?c&~is ?v $?))
   =>
   (retract ?f)
   (println "In rule " ?name ", if portion comparator should be \"is\"" crlf
            "   " ?a " " ?c " " ?v " "))
               
(defrule VALIDATE::illegal-variable-value
   ?f <- (rule (name ?name) (validate yes)
               (if ?a ?c ?v $?))
   (question (variable ?a) (valid-answers))
   (legalanswers (values $?values))
   (test (not (member$ ?v ?values)))
   =>
   (retract ?f)
   (println "In rule " ?name ", the value " ?v " is not legal for variable " ?a ":" crlf
            "   " ?a " " ?c " " ?v))               

(defrule VALIDATE::reachable
   (rule (name ?name) (validate yes)
         (if ?a ?c ?v $?))
   (not (question (variable ?a)))
   (not (rule (then ?a $?)))
   =>
   (println "In rule " ?name " no question or rule could be found "
               "that can supply a value for the variable " ?a ":" crlf
               "   " ?a " " ?c " " ?v))

(defrule VALIDATE::used "TBD lower salience"
   ?f <- (rule (name ?name) (validate yes)
               (then ?a is ?v))
   (not (goal (variable ?a)))
   (not (rule (if ?a ? ?v $?)))
   =>
   (retract ?f)
   (println "In rule " ?name " the conclusion for variable " ?a 
            " is neither referenced by any rules nor the primary goal" crlf
            "   " ?a " is " ?v))
               
(defrule VALIDATE::variable-in-both-if-and-then
   ?f <- (rule (name ?name) (validate yes)
               (if ?a $?)
               (then ?a is ?v))
   =>
   (retract ?f)
   (println "In rule " ?name " the variable " ?a 
            " is used in both the if and then sections"))
                              
(defrule VALIDATE::question-variable-unreferenced
   (question (variable ?a) (query ?q))
   (not (rule (validate done) (if $? ?a is ?v $?)))
   =>
   (println "The question \"" ?q "\", assigns a value to the variable " ?a 
            " which is not referenced by any rules"))

;;;***************************
;;;* DEFFACTS KNOWLEDGE BASE *
;;;***************************

(deffacts MAIN::knowledge-base 
   (goal (variable respuesta))
   (legalanswers (values yes no))
   (rule (if poneHuevos is yes) 
         (then tipo is poneHuevos))
   (rule (if poneHuevos is no) 
         (then tipo is mamifero))
   (question (variable poneHuevos)
             (query "tu animal pone huevos?"));;;el animal pone huevos?
   (rule (if tipo is poneHuevos and
          alas is no) 
         (then respuesta is salamandra))
   (rule (if tipo is poneHuevos and
          alas is yes)
          (then tipo2 is ave))
   ;(rule (if tipo is mamifero) 
    ;     (then respuesta is esMamifero));;;aqui empieza toda la linea de mamifero
   (rule (if tipo is mamifero and comeCarne is yes) 
         (then tipo2 is carnivoro))
   (rule (if tipo is mamifero and comeCarne is no) 
         (then tipo2 is ungulado))
   (question (variable comeCarne)
         (query "tu animal come carne?"));;;

   (rule (if tipo2 is carnivoro and manchas is yes) 
         (then respuesta is leopardo))
   (rule (if tipo2 is carnivoro and  manchas is no) 
         (then respuesta is tigre))
   (question (variable manchas)
         (query "tu animal tiene manchas?"));;;

   (rule (if tipo2 is ungulado and cuelloLargo is yes) 
         (then respuesta is jirafa))
   (rule (if tipo2 is ungulado and  cuelloLargo is no) 
         (then respuesta is cebra))
   (question (variable cuelloLargo)
         (query "tu animal tiene cuello largo?"));;;

      



   ;;;Reptil/Ave      
   (question (variable alas)
             (query "tu animal tiene alas?"));;;es un animal con alas?
   (rule (if tipo2 is ave and vuela is yes) 
         (then tipo3 is volador))
   (rule (if tipo2 is ave and vuela is no) 
         (then tipo3 is NOvolador))
   (question (variable vuela)
             (query "tu animal vuela?"));;;es un animal que vuela?
   (rule (if tipo3 is volador and comeAves is yes) 
         (then respuesta is halconPeregrino))
   (rule (if tipo3 is volador and comeAves is no) 
         (then respuesta is albatros))
   (question (variable comeAves)
             (query "tu animal come aves?"));;;es un animal que come aves?
   (rule (if tipo3 is NOvolador and nada is yes) 
         (then respuesta is pinguino ))
   (rule (if tipo3 is NOvolador and nada is no) 
         (then respuesta is avestruz))
   (question (variable nada)
             (query "tu animal nada?"));;;es un animal que nada?
   (answer (prefix "I think your animal is a ") (variable respuesta) (postfix ".")))

