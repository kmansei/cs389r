(include-book "std/util/define" :dir :system)


(define true-listp2 (x)
  :ruler-extenders :basic
  :guard t
  :hints
  (("Goal" :induct (true-listp2 x)))
       (if (consp x)
           (true-listp2 (cdr x))
           (eq x nil)))#|ACL2s-ToDo-Line|#


(verify (not (true-listp2 x)))

(fty::deftypes arithmetic-terms
  (fty::deftagsum aterm
    (:num ((val integerp)))
    (:sum ((args atermlist))))
  (fty::deflist atermlist :elt-type aterm))

#|
(defines aterm-eval
  (define aterm-eval ((x aterm-p))
    :measure (aterm-count x)
    :returns (val integerp)
    :verify-guards nil
    (aterm-case x
                :num x.val
                :sum (atermlist-sum x.args)))
  (define atermlist-sum ((x atermlist-p))
    :measure (atermlist-count x)
    :returns (val integerp)
    (if (atom x)
      0
      (+ (aterm-eval (car x))
         (atermlist-sum (cdr x)))))
  ///
  (verify-guards aterm-eval))

(defun aterm-eval-ind (x)
  (if (atom x)
    (list x)
    (list (aterm-eval-ind (car x))
          (aterm-eval-ind (cdr x)))))
|#

(defun subst-term-flag (flag x alist)
(case flag
(subst-term
(cond (( not x ) nil )
((symbolp x ) ; ; variable
(cdr ( assoc-equal x alist )))
((atom x ) nil ) ; ; malformed
((eq (car x) 'quote) x)
(t ; ; function or lambda call
(cons (car x)
(subst-term-flag 'subst-termlist (cdr x) alist)))))
(t ; ; subst-termlist
(if (atom x)
nil
(cons (subst-term-flag 'subst-term (car x) alist)
(subst-term-flag 'subst-termlist (cdr x) alist))))))

(thm (IMPLIES (CONSP X)
         (< (ATERM-COUNT (CAR X))
            (ATERM-COUNT X))))

(define aterm-eval (flag (x aterm-p))
  :measure (aterm-count x)
  :verify-guards nil
  (case flag
        (0
         (aterm-case x
                     :num x.val
                     :sum (aterm-eval 1 x.args)))
        (1
         (if (atom x)
           0
           (+ (aterm-eval 0 (car x))
              (aterm-eval 1 (cdr x)))))))
          
(defun aterm-eval-ind (x)
  (if (atom x)
    (list x)
    (list (aterm-eval-ind (car x))
          (aterm-eval-ind (cdr x)))))


(defthm aterm-theorem
  (and (<= 0 (aterm-eval x))
       (<= 0 (atermlist-sum x)))
  :hints (("goal" :induct (aterm-eval-ind x)
                  :expand (aterm-eval x))))

(defthm aterm-theorem
  (and (<= 0 (aterm-eval x)))