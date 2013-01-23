;;; -*- Mode: LISP; Package: (SCREAMER-USER :USE CL :COLON-MODE :EXTERNAL); Base: 10; Syntax: Ansi-common-lisp -*-

;;; LaHaShem HaAretz U'Mloah

;;; This is a pedagogical implementation of the SNLP planning algorithm due to
;;; McAllester & Rosenblitt (1991). To run it on the Sussman anomaly evaluate:
;;; (time
;;;  (null (one-value (print (nonlinear-planner (lifted-sussman-anomaly))))))

(in-package :screamer-user)
(shadow 'step)

(defstruct (operator (:conc-name nil) (:print-function print-operator))
  name
  preconditions
  delete-list
  add-list
  cost)

(defstruct (planning-problem (:conc-name nil))
  operators
  sigma
  omega)

(defstruct (causal-link (:conc-name nil) (:print-function print-causal-link))
  s
  p
  w)

(defstruct (step (:conc-name nil))
  operator
  step-name
  steps-preceeding
  steps-following)

(defstruct (nonlinear-plan (:conc-name nil)
			   (:print-function print-nonlinear-plan))
  steps
  causal-links)

(defun print-operator (operator stream print-level)
 (declare (ignore print-level))
 (format stream "~%[Operator")
 (format stream "~% Name: ~S" (name operator))
 (format stream "~% Preconditions:")
 (dolist (p (preconditions operator)) (format stream "~%  ~S" p))
 (format stream "~% Delete List:")
 (dolist (p (delete-list operator)) (format stream "~%  ~S" p))
 (format stream "~% Add List:")
 (dolist (p (add-list operator)) (format stream "~%  ~S" p))
 (format stream "~% Cost: ~D]" (cost operator)))

(defun print-causal-link (l stream print-level)
 (declare (ignore print-level))
 (format stream "~S ->~S ~S" (step-name (s l)) (p l) (step-name (w l))))

(defun print-nonlinear-plan (plan stream print-level)
 (declare (ignore print-level))
 (format stream "~%[Nonlinear Plan")
 (format stream "~% Steps:")
 (dolist (u (steps plan))
  (format stream "~%  ~S: ~S" (step-name u) (name (operator u))))
 (format stream "~% Causal Links:")
 (dolist (l (causal-links plan)) (format stream "~%  ~S" l))
 (format stream "~% Safety Conditions:")
 (dolist (u (steps plan))
  (dolist (v (steps-preceeding u))
   (format stream "~%  ~S<~S" (step-name v) (step-name u))))
 (format stream "]"))

;;;(defun equal? (x y) (equal x y))

(defun equal? (x y) (decide (equalv x y)))

(defun member? (x set)
 (and (not (null set)) (or (equal? x (first set)) (member? x (rest set)))))

(defun make-plan-step (operator plan)
 (make-step :step-name (intern (format nil "S~D" (length (steps plan))))
	    :operator operator))

(defun before? (u v) (member u (steps-preceeding v) :test #'eq))

(defun assert-before! (u v)
 (if (eq u v) (fail))
 (unless (before? u v)
  (local (setf (steps-preceeding v) (cons u (steps-preceeding v)))
	 (setf (steps-following u) (cons v (steps-following u))))
  (dolist (w (steps-preceeding u)) (assert-before! w v))
  (dolist (w (steps-following v)) (assert-before! u w))))

(defun open-precondition (plan)
 (local (dolist (w (steps plan))
	 (dolist (p (preconditions (operator w)))
	  (block again
	   (dolist (l (causal-links plan))
	    (if (and (eq w (w l)) (equal? p (p l))) (return-from again)))
	   (return-from open-precondition (values w p)))))))

(defun add-causal-link! (s p w plan)
 (unless (and (member? p (add-list (operator s)))
	      (member? p (preconditions (operator w))))
  (fail))
 (assert-before! s w)
 (local (setf (causal-links plan)
	      (cons (make-causal-link :s s :p p :w w) (causal-links plan)))))

(defun threat (plan)
 (local (dolist (u (steps plan))
	 (dolist (l (causal-links plan))
	  (if (and (not (eq u (s l)))
		   (not (eq u (w l)))
		   (not (before? (w l) u))
		   (not (before? u (s l)))
		   (or (member? (p l) (add-list (operator u)))
		       (member? (p l) (delete-list (operator u)))))
	      (return-from threat (values l u)))))))

(defun find-completion (plan c operators)
 (multiple-value-bind (w p) (open-precondition plan)
  (if w
      (either (progn (add-causal-link! (a-member-of (steps plan)) p w plan)
		     (find-completion plan c operators))
	      (progn (unless (> c 0) (fail))
		     (let* ((operator (funcall-nondeterministic operators))
			    (s (make-plan-step operator plan)))
		      (local (setf (steps plan) (cons s (steps plan))))
		      (add-causal-link! s p w plan)
		      (find-completion plan (- c (cost operator)) operators))))
      (multiple-value-bind (l u) (threat plan)
       (if l
	   (progn (either (assert-before! u (s l)) (assert-before! (w l) u))
		  (find-completion plan c operators))
	   plan)))))

(defun initial-nonlinear-plan (sigma omega)
 (let ((start (make-step :step-name 'start
			 :operator (make-operator :name 'start
						  :add-list sigma)))
       (finish (make-step :step-name 'finish
			  :operator (make-operator :name 'finish
						   :preconditions omega))))
  (assert-before! start finish)
  (make-nonlinear-plan :steps (list start finish))))

(defun nonlinear-planner (problem)
 (find-completion (initial-nonlinear-plan (sigma problem) (omega problem))
		  (an-integer-above 0)
		  (operators problem)))

(defun blocks-operator (blocks)
 (let ((x (a-member-of blocks))
       (y (a-member-of blocks))
       (z (a-member-of blocks)))
  (if (or (eq x y) (eq x z) (eq y z)
	  (member x '(table-spot1 table-spot2 table-spot3) :test #'eq))
      (fail))
  (make-operator :name `(move ,x ,y ,z)
		 :preconditions `((clear ,x) (clear ,z) (on ,x ,y))
		 :delete-list `((clear ,z) (on ,x ,y))
		 :add-list `((clear ,y) (on ,x ,z))
		 :cost 1)))

(defun lifted-blocks-operator ()
 (let ((x (make-variable))
       (y (make-variable))
       (z (make-variable)))
  (assert! (andv (notv (equalv x y))
		 (notv (equalv x z))
		 (notv (equalv y z))
		 (notv (memberv x '(table-spot1 table-spot2 table-spot3)))))
  (make-operator :name `(move ,x ,y ,z)
		 :preconditions `((clear ,x) (clear ,z) (on ,x ,y))
		 :delete-list `((clear ,z) (on ,x ,y))
		 :add-list `((clear ,y) (on ,x ,z))
		 :cost 1)))

(defun ground-sussman-anomaly ()
 (make-planning-problem
  :operators #'(lambda ()
		(blocks-operator
		 '(a b c table-spot1 table-spot2 table-spot3)))
  :sigma '((on c a) (on b table-spot1) (on a table-spot2)
	   (clear b) (clear c) (clear table-spot3))
  :omega '((on a b) (on b c))))

(defun lifted-sussman-anomaly ()
 (make-planning-problem
  :operators #'lifted-blocks-operator
  :sigma '((on c a) (on b table-spot1) (on a table-spot2)
	   (clear b) (clear c) (clear table-spot3))
  :omega '((on a b) (on b c))))

;;; Tam V'Nishlam Shevah L'El Borei Olam
