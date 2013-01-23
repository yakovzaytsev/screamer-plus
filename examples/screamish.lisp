;-*- Mode: Common-lisp; Package: :screamer; -*-
(in-package :screamer)
;;;$Id: screamish.lisp,v 1.5 2004/03/10 04:10:19 dvm Exp $

(eval-when (:load-toplevel :slurp-toplevel)
   (export '(screamer-solve screamer-funs* screamer-preds*)))

;;;;(eval-when (:compile-toplevel :slurp-toplevel)
;;;;   (import '(optop::=~ optop::/=~ optop::=<)))

(defun screamer-solve (constraints vars)
   (one-value
      (let ((soln
	       (solution
		  (progn
		     (dolist (c constraints)
			(constraint-impose c))
		     vars)
		  (reorder #'range-size
			   #'(lambda (x) (< x 1e-6))
			   #'>
			   #'divide-and-conquer-force))))
	(mapcar #'(lambda (v)
		     (cond ((variable? v)
			    (/ (+ (variable-lower-bound v)
				  (variable-upper-bound v))
			       2))
			   (t v)))
		soln))
      ':no-solution))

(defvar screamer-funs* '(+ - * /))

(defvar screamer-preds* '(> >= < optop::=< <= optop::=~ optop::/=~))

(defun constraint-impose (constraint)
   (cond ((variable? constraint)
	  constraint)
	 ((atom constraint)
	  constraint)
	 ((eq (car constraint) 'same-sign)
	  (orv (andv (> (cadr constraint) 0)
		     (> (caddr constraint) 0))
	       (andv (< (cadr constraint) 0)
		     (< (caddr constraint) 0))))
	 ((member (car constraint) screamer-funs*)
	  (apply 
	     (case (car constraint)
		(+ #'+v)
		(- #'-v)
		(* #'*v)
		(/ #'/v))
	     (mapcar #'constraint-impose (cdr constraint))))
	 ((member (car constraint) screamer-preds*)
	  (assert!
	      (apply
	         (case (car constraint)
		    (> #'>v)
		    (>= #'>=v)
		    (< #'<v)
		    ((optop::=< <=) #'<=v)
		    (optop::=~ #'=v)
		    (optop::/=~ #'/=v))
		 (mapcar #'constraint-impose (cdr constraint)))))
	 (t
	  (error "Unintelligible constraint: ~s" constraint))))
	  
(defvar v5*)

(setq v5* (an-integer-betweenv 0 10 'v5*))

(defun scr-test ()
  (for-effects
     (print
	(solution
	   (let ((v2 (a-real-betweenv 5.0 10.0 'v2))
		 (v3 (a-real-betweenv 5.0 10.0 'v3))
		 ;;;;(v5 (an-integer-betweenv 0 10 'v5))
		 )
	      (let ((vl (list v2 v3 v5*)))
		 (assert!
		    (andv (=v (apply #'+v (list v2 1.0))
			      v3)
			  (=v (*v 2.0 v3)
			      (apply #'+v (list v2 8.0)))))
		 (assert!
		     (andv
			  (>v v5* v2)
			  (<v v5* (*v 1.2 v3))))
		 vl))
	   (reorder #'range-size
		    #'(lambda (x) (< x 1e-6))
		    #'>
		    #'divide-and-conquer-force)))))

(defvar soln*)

(defun scr-one ()
  (one-value
     (let ((soln
	      (solution
		 (let ((v2 (a-real-betweenv 5.0 10.0 'v2))
		       (v3 (a-real-betweenv 5.0 10.0 'v3))
		       ;;;;(v5 (an-integer-betweenv 0 10 'v5))
		       )
		    (assert!
		       (andv (=v (+v v2 1.0)
				 v3)
			     (=v (*v 2.0 v3)
				 (+v v2 8.0))))
		    (assert!
			(andv
			     (>v v5* v2)
			     (<v v5* (*v 1.2 v3))))
		    (list v2 v3 v5*))
		 (reorder #'range-size
			  #'(lambda (x) (< x 1e-6))
			  #'>
			  #'divide-and-conquer-force))))
        (mapcar #'(lambda (v)
		     (cond ((variable? v)
			    (list (variable-lower-bound v)
				  (variable-upper-bound v)))
			   (t v)))
		soln))))
