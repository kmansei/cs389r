;(include-book "tools/defsum" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/top" :dir :system)
(set-ignore-ok :warn)

;Expression
(fty::deftypes expression
  (fty::deftagsum expr
                  (:VAR ((v stringp)))
                  (:FIELD ((obj expr-p)
                           (field stringp)))
                  (:NEW ((class stringp)
                         (args exprlist)))
                  (:INVK ((obj expr-p)
                          (method stringp)
                          (args exprlist))))
  (fty::deflist exprlist :elt-type expr))

;Guard (("a" . "A") ("b" . "B") ... )
(defun string-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
    (equal x nil)
    (and (consp (car x))
         (stringp (caar x))
         (stringp (cdar x))
         (string-alistp (cdr x)))))

;Method
(std::defaggregate fj_method
  ((returnType stringp       :rule-classes :type-prescription)
   (name       stringp       :rule-classes :type-prescription)
   (params     string-alistp :rule-classes :type-prescription)
   (body       expr-p        :rule-classes :type-prescription))
  :tag :method
  )

;Guard
(define method-listp (x)
  (if (atom x)
    (equal x nil)
    (and (fj_method-p (car x))
         (stringp (fj_method->returnType (car x)))
         (stringp (fj_method->name (car x)))
         (string-alistp (fj_method->params (car x)))
         (expr-p (fj_method->body (car x)))
         (method-listp (cdr x)))))

;Constructor
(std::defaggregate fj_constructor
  ((returnType       stringp       :rule-classes :type-prescription)
   (params           string-alistp :rule-classes :type-prescription)
   (inits            string-listp  :rule-classes :type-prescription))
  :tag :constructor
  )

;Class
(std::defaggregate fj_class
  ((name          stringp          :rule-classes :type-prescription)
   (fields        string-alistp    :rule-classes :type-prescription)
   (constructor   fj_constructor-p :rule-classes :type-prescription)
   (methods       method-listp      :rule-classes :type-prescription))
  :tag :class
  )

; Γ(x) = "C"
(define getTypeFromCtxt ((ctxt string-alistp) (var stringp))
  (if (consp ctxt)
    (if (equal (caar ctxt) var)
      (cdar ctxt)
      (getTypeFromCtxt (cdr ctxt) var))
    nil))

;FieldType(fields, f) = C
(define getFieldType (fields fieldname)
  :guard (and (stringp fieldname)
              (string-alistp fields))
  (if (consp fields)
    (if (equal (caar fields) fieldname)
      (cdar fields)
      (getFieldType (cdr fields) fieldname))
    nil))

; constructor guard
(define const-p (x)
  (and (fj_constructor-p x)
       (stringp (fj_constructor->returnType x))
       (string-listp (fj_constructor->inits x))))

; class guard
(define class-listp (x)
  (if (consp x)
    (and (fj_class-p (car x))
         (stringp (fj_class->name (car x)))
         (string-alistp (fj_class->fields (car x)))
         (const-p (fj_class->constructor (car x)))
         (method-listp (fj_class->methods (car x)))
         (class-listp (cdr x)))
    (equal x nil)))

; θ_f (C) = (("f1" . "C1") ("f2" . "C2") ... ("fn" . "Cn"))
(define fields (classDefs classname)
  :guard (and (stringp classname)
              (class-listp classDefs))
  :guard-hints (("Goal" :expand (class-listp classDefs)))
  (if (consp classDefs)
    (if (equal (fj_class->name (car classDefs))
               classname)
      (fj_class->fields (car classDefs))
      (fields (cdr classDefs) classname))
    nil))

; (("f1" . "C") ("f2" . "C2") ... ("fn" . "Cn")) -> (C_1 ... C_n)
(define getTypesFromParams (params)
  :guard (string-alistp params)
  (if (atom params)
    nil
    (cons (cdar params) (getTypesFromParams (cdr params)))))

; θ_m(C) = m_1...m_n
(define getMethodList (classDefs classname)
  :guard (and (stringp classname)
              (class-listp classDefs))
  :guard-hints (("Goal" :expand (class-listp classDefs)))
  (if (consp classDefs)
    (if (equal (fj_class->name (car classDefs))
               classname)
      (fj_class->methods (car classDefs))
      (getMethodList (cdr classDefs) classname))
    nil))

; getMethod(<m_1>...<m_n>, m_i) = <m_i>
(define getMethod (methodlist methodname)
  :guard (and (stringp methodname)
              (method-listp methodlist))
  :guard-hints (("Goal" :expand (method-listp methodlist)))
  (if (consp methodlist)
    (if (equal (fj_method->name (car methodlist))
               methodname)
      (car methodlist)
      (getMethod (cdr methodlist) methodname))
    nil))

; Type Checker
; typeof(θ, Γ, e) = T
; if x cannot be typed, return T = nil
(defines typeof
  (define typeof (classDefs ctxt e)
    :measure (expr-count e)
    :guard (and (class-listp classDefs)
                (string-alistp ctxt)
                (expr-p e))
    :guard-hints (("Goal" :expand (class-listp classDefs)))
    :verify-guards nil
    (expr-case e
               :VAR (getTypeFromCtxt ctxt e.v)
               :FIELD (let ((e-type (typeof classDefs ctxt e.obj)))
                         (getFieldType (fields classDefs e-type) e.field))
               :NEW (let ((type-list (getTypesFromParams (fields classDefs e.class))))
                      (if (equal (typeof-list classDefs ctxt e.args) 
                                 type-list)
                        e.class
                        nil))
               :INVK (let ((objtype (typeof classDefs ctxt e.obj)))
                       (let ((mlist (getMethodList classDefs objtype)))
                         (if (equal (typeof-list classDefs ctxt e.args)
                                    (getTypesFromParams (fj_method->params (getMethod mlist e.method))))
                           (fj_method->returnType (getMethod mlist e.method))
                           nil)))))
  ;typeof-list(θ, Γ, (e_1...e_n)) = (T_1...T_n)
  (define typeof-list (classDefs ctxt e-list)
    :measure (exprlist-count e-list)
    :guard (and (exprlist-p e-list)
                (class-listp classDefs)
                (string-alistp ctxt))
    (if (atom e-list)
      nil
      (cons (typeof classDefs ctxt (car e-list))
            (typeof-list classDefs ctxt (cdr e-list))))))

; method typing
(define t-method (classDefs classname m)
  :verify-guards nil
  (equal (fj_method->returnType m)
         (typeof classDefs
                 (list (fj_method->params m)
                       (cons "this" classname))
                 (fj_method->body m))))

; method-list typing
(define t-method-list (classDefs classname mlist)
  :verify-guards nil
  (if (atom mlist)
    t
    (and (t-method classDefs classname (car mlist))
         (t-method-list classDefs classname (cdr mlist)))))

; Class Typing
(define t-class-list (classDefs)
  :verify-guards nil
  (if (atom classDefs)
    t
    (and (t-method-list classDefs
                        (fj_class->name (car classDefs))
                        (fj_class->methods (car classDefs)))
         (t-class-list (cdr classDefs)))))

;Value
; v = new C(v_1,...,v_n)
(defines isvalue
  (define isvalue (e)
    :measure (expr-count e)
    :guard (expr-p e)
    (case (expr-kind e)
          (:NEW (isvaluelist (expr-new->args e)))))
  (define isvaluelist (args)
    :measure (exprlist-count args)
    :guard (exprlist-p args)
    (if (atom args)
      (equal nil args)
      (and (isvalue (car args))
           (isvaluelist (cdr args))))))

;getithField(e_1...e_n, fields, field_i) -> e_i
(define getithField (args fields field)
  :guard (and (exprlist-p args)
              (string-alistp fields)
              (stringp field))
  (if (atom args)
    nil
    (if (equal (caar fields) field)
      (car args)
      (getithField (cdr args) (cdr fields) field))))

(define getArgs (e)
  :guard (expr-p e)
  (case (expr-kind e)
        (:NEW (expr-new->args e))
        (otherwise nil)))

(define getclassname (e)
  :guard (expr-p e)
  (case (expr-kind e)
        (:NEW (expr-new->class e))
        (otherwise nil)))

; [args/params, this/"this"]e
(defines substitution
  (define substitution (e params args this)
    :measure (expr-count e)
    :guard (and (expr-p e)
                (string-listp params)
                (exprlist-p args)
                (expr-p this))
    :verify-guards nil
    (expr-case e
               :VAR (let ((index (search (list e.v) params)))
                      (if index
                        (nth index args)
                        (if (equal e.v "this")
                          this
                          e)))
               :FIELD (expr-field (substitution e.obj params args this)
                                  e.field)
               :NEW (expr-new e.class (subst-list e.args params args this))
               :INVK (expr-invk (substitution e.obj params args this)
                                e.method
                                (subst-list e.args params args this))))
  (define subst-list (e-list params args this)
    :measure (exprlist-count e-list)
    :guard (and (exprlist-p e-list)
                (expr-p this)
                (string-listp params)
                (exprlist-p args))
    (if (atom e-list)
      nil
      (cons (substitution (car e-list) params args this)
            (subst-list (cdr e-list) params args this)))))

;(("f1" . "C") ("f2" . "C2") ... ("fn" . "Cn")) -> (f_1 ... f_n)
(define getVarArgs (params)
  :guard (string-alistp params)
  (if (atom params)
    nil
  (cons (caar params) (getVarArgs (cdr params)))))

; Evaluate by 1 step
; Return nil if eval doesn't happen
(defines eval-expr
  (define eval-expr (classDefs e)
      :measure (expr-count e)
      :guard (and (expr-p e)
                  (class-listp classDefs))
      :verify-guards nil
      (expr-case e
                 :FIELD (if (isvalue e.obj)
                          (let ((val (eval-expr classDefs e.obj)))
                            (expr-case val
                                     :NEW (getithField val.args
                                                       (fields classDefs val.class)
                                                       e.field)
                                     :otherwise nil))
                            (expr-field (eval-expr classDefs e.obj) e.field))
                 :NEW (expr-new e.class (eval-exprlist classDefs e.args))
                 :INVK (if (isvalue e.obj)
                         (if (isvaluelist e.args)
                           (expr-case e.obj
                                      :NEW (let ((method (getMethod (getMethodList classDefs e.obj.class)
                                                                    e.method)))
                                             (substitution (fj_method->body method)
                                                           (getVarArgs (fj_method->params method))
                                                           e.args
                                                           e.obj))
                                      :otherwise nil)
                           (expr-invk e.obj e.method (eval-exprlist classDefs e.args)))
                         (expr-invk (eval-expr classDefs e.obj) e.method e.args))
                 :otherwise nil))
  (define eval-exprlist (classDefs e-list)
    :measure (exprlist-count e-list)
    (if (atom e-list)
      nil
      (cons (eval-expr classDefs (car e-list))
            (eval-exprlist classDefs (cdr e-list))))))

; Theorems
(defthm ctxt-cdr
  (implies (and (CONSP E-LIST)
                (NOT (EQUAL FLAG 'TYPEOF))
                (typeof-list classDefs (cdr ctxt) e-list))
           (typeof-list classDefs ctxt e-list))
  :hints (("Goal" :expand (typeof-list classDefs ctxt e-list))))

(DEFTHM CTXT-CDR2
        (IMPLIES (AND (FLAG-IS 'TYPEOF-LIST)
                      (NOT (EQUAL FLAG 'TYPEOF))
                      (NOT (CONSP E-LIST))
                      (TYPEOF-LIST CLASSDEFS (CDR CTXT)
                                   E-LIST))
                 (TYPEOF-LIST CLASSDEFS CTXT E-LIST))
        :INSTRUCTIONS (:PROMOTE :X (:DEMOTE 4)
                                (:DV 1)
                                :X
                                :TOP :S))

(make-flag typeof-flag typeof)#|ACL2s-ToDo-Line|#


#|
; Weakening Lemma
; if Γ⊢e:T then Γ,x:S⊢e:T
(defthm-typeof-flag
  (defthm weakening-term
    (implies (typeof classDefs (cdr ctxt) e)
             (typeof classDefs ctxt e))
    :rule-classes :type-prescription
    :flag typeof)
  (defthm weakening-list
    (implies (typeof-list classDefs (cdr ctxt) e-list)
             (typeof-list classDefs ctxt e-list))
    :rule-classes :type-prescription
    :flag typeof-list))
|#

;; Progress Theorem
; if ⊢e:T and ⊢CL then e->e' or e is value  

#|
(defthm-typeof-flag
  (defthm progress-term
    (implies (and (class-listp classDefs)
                  (expr-p e)
                  (typeof classDefs nil e)
                  (t-class-list classDefs))
             (or (isvalue e)
                 (eval-expr classDefs e)))
    :rule-classes :type-prescription
    :flag typeof)
  (defthm progress-list
    (implies (and (class-listp classDefs)
                  (exprlist-p e-list)
                  (typeof-list classDefs nil e-list)
                  (t-class-list classDefs))
             (or (isvaluelist e-list)
                 (eval-exprlist classDefs e-elist)))
    :rule-classes :type-prescription
    :flag typeof-list))
|#

; Preservation Theorem
; if ⊢e:T and ⊢CL and e->e' then e':T
#|
(defthm-typeof-flag
  (defthm preservation-term
    (implies (and (class-listp classDefs)
                  (expr-p e)
                  (typeof classDefs nil e)                 ; type(e) = T
                  (eval-expr classDefs e)                  ; eval(e) = e' 
                  (t-class-list classDefs))
             (equal (typeof classDefs nil e)               ; type(e) = type((eval(e)))
                    (typeof classDefs nil (eval-expr classDefs e))))
    :rule-classes :type-prescription
    :flag typeof)
  (defthm preservation-list
    (implies (and (class-listp classDefs)
                  (exprlist-p e-list)
                  (typeof-list classDefs nil e-list)
                  (eval-exprlist classDefs e-list)
                  (t-class-list classDefs))
             (equal (typeof-list classDefs nil e-list)
                    (typeof-list classDefs nil (eval-exprlist classDefs e-list))))
    :rule-classes :type-prescription
    :flag typeof-list))
|#

