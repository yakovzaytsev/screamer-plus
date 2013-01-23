(in-package :t2l)

(define-box om-all-memberv (x sequence &optional (remove-nil t))
  :initvals '(nil nil t)
  :indoc '("" "" "")
  :icon 324
  :doc ""
  (cond ((null x) (memberv nil sequence))
        ((listp x) 
         (apply #'andv (mapcar #'(lambda (y) (memberv y sequence))
                               (if remove-nil
                                   (remove-nil (flat x))
                                 (flat x)))))
        (t (memberv x sequence))))
	
(define-box list-nsucc-span-betweenv ((list list) (n integer) (step integer) (min integer) (max integer))
  :initvals '((1 2 4 8 16) 2 1 1 8)
  :indoc '("" "" "" "" "")
  :icon 324
  :doc ""
  (apply #'andv
         (mapcar #'(lambda (x)
                     (let ((group (remove-nil (flat x))))
                       (cond (group
                              (let ((group-min (apply #'minv group))
                                    (group-max (apply #'maxv group)))
                                (let ((span (-v group-max group-min)))
                                  (if (>= *mess* 40) (lprint 'list-nsucc-span-betweenv 'span span))
                                  (andv (<=v span max)
                                        (>=v span min)))))
                             (t t))))
                     (nsucc (flat list) n :step step))))

(cl:defun list-nsucc-funcallv (fn list n)
  (apply #'andv (mapcar fn (nsucc (remove-nil (flat list)) n :step n))))

(define-box list-nsucc>v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all>v list n))

(define-box list-nsucc>=v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all>=v list n))

(define-box list-nsucc<v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all<v list n))

(define-box list-nsucc<=v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all<=v list n))

(define-box list-nsucc<>v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'(lambda (x)
                           (orv (all<v x)
                                (all>v x)))
                       list
                       n))

(define-box list-nsucc<>=v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'(lambda (x)
                           (orv (all<=v x)
                                (all>=v x)))
                       list
                       n))

(define-box list-nsucc=v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all=v list n))

(define-box list-nsucc/=v ((list list) (n integer))
  :initvals '((1 2 3 4 5 6 7) 3)
  :indoc '("" "")
  :icon 324
  :doc ""
  (list-nsucc-funcallv #'all/=v list n))