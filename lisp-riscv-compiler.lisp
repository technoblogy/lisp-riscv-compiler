; Lisp compiler to RISC-V Assembler - Version 1 - 11th October 2024
;

#|
Language definition:

Defining variables and functions: defun, setq
Symbols: nil, t
List functions: car, cdr
Arithmetic functions: +, -, *, /, mod, 1+, 1-
Arithmetic comparisons: =, <, <=, >, >=, /=
Conditionals: if, and, or
|#

; Compile a lisp function

(defun compiler (name)
  (if (eq (car (eval name)) 'lambda)
      (eval (comp (cons 'defun (cons name (cdr (eval name))))))
    (error "Not a Lisp function")))

; The main compile routine - returns compiled code for x, prefixed by type :integer or :boolean
; Leaves result in a0

(defun comp (x &optional env tail)
  (cond
   ((null x) (type-code :boolean '(($li 'a0 0))))
   ((eq x t) (type-code :boolean '(($li 'a0 1))))
   ((symbolp x) (comp-symbol x env))
   ((atom x) (type-code :integer (list (list '$li ''a0 x))))
   (t (let ((fn (first x)) (args (rest x)))
        (case fn
          (defun (setq *label-num* 0)
                 (setq env (mapcar #'(lambda (x y) (cons x y)) (second args) *locals*))
                 (comp-defun (first args) (second args) (cddr args) env))
          (progn (comp-progn args env tail))
          (if    (comp-if (first args) (second args) (third args) env tail))
          (setq  (comp-setq args env tail))
          (t     (comp-funcall fn args env tail)))))))

; Utilities

(defun push-regs (&rest regs)
  (let ((n -4))
  (append
   (list (list '$addi ''sp ''sp (* -4 (length regs))))
   (mapcar #'(lambda (reg) (list '$sw (list 'quote reg) (incf n 4) ''(sp))) regs))))

(defun pop-regs (&rest regs)
  (let ((n (* 4 (length regs))))
  (append
   (mapcar #'(lambda (reg) (list '$lw (list 'quote reg) (decf n 4) ''(sp))) regs)
   (list (list '$addi ''sp ''sp (* 4 (length regs)))))))

; Like mapcon but not destructive

(defun mappend (fn lst)
  (apply #'append (mapcar fn lst)))

; The type is prefixed onto the list of assembler code instructions

(defun type-code (type code) (cons type code))

(defun code-type (type-code) (car type-code))

(defun code (type-code) (cdr type-code))

(defun checktype (fn type check)
  (unless (or (null type) (null check) (eq type check))
    (error "Argument to '~a' must be ~a not ~a" fn check type)))

; Allocate registers -  s0, s1, and a0 to a5 give compact instructions

(defvar *params* '(a0 a1 a2 a3))

(defvar *locals* '(a4 a5 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))

(defvar *used-params* nil)

; Generate a label

(defvar *label-num* 0)

(defun gen-label ()
  (read-from-string (format nil "lab~d" (incf *label-num*))))

; Subfunctions

(defun comp-symbol (x env)
  (let ((reg (cdr (assoc x env))))
    (type-code nil (list (list '$mv ''a0 (list 'quote reg))))))

(defun comp-setq (args env tail)
  (let ((value (comp (second args) env tail))
        (reg (cdr (assoc (first args) env))))
    (type-code 
     (code-type value) 
     (append (code value) (list (list '$mv (list 'quote reg) ''a0))))))

(defun comp-defun (name args body env)
  (setq *used-params* (subseq *locals* 0 (length args)))
  (append 
   (list 'defcode name args)
   (list name)
   (apply #'append 
          (mapcar #'(lambda (x y) (list (list '$mv (list 'quote x) (list 'quote y))))
                  *used-params* *params*))
   (code (comp-progn body env t))))

(defun comp-progn (exps env tail)
  (let* ((len (1- (length exps)))
         (nlast (subseq exps 0 len))
         (last1 (nth len exps))
         (start (mappend #'(lambda (x) (append (code (comp x env t)))) nlast))
         (end (comp last1 env tail)))
    (type-code (code-type end) (append start (code end)))))

(defun comp-if (pred then else env tail)
  (let ((lab1 (gen-label))
        (lab2 (gen-label))
        (test (comp pred env nil)))
    (checktype 'if (car test) :boolean)
    (type-code :integer
               (append
                (code test) (list (list '$beqz ''a0 lab1))
                (code (comp then env t)) (list (list '$j lab2) lab1)
                (code (comp else env tail)) (list lab2)
                (when tail '(($ret)))))))

(defun $sgt (rd rs1 rs2)
  ($slt rd rs2 rs1))

(defun comp-funcall (f args env tail)
  (let ((test (assoc f '((< . $slt) (> . $sgt))))
        (teste (assoc f '((= . $seqz) (/= . $snez))))
        (testn (assoc f '((>= . $slt) (<= . $sgt))))
        (logical (assoc f '((and . $and) (or . $or))))
        (arith1 (assoc f '((1+ . 1) (1- . -1))))
        (arith (assoc f '((+ . $add) (- . $sub) (* . $mul) (/ . $div) (mod . $rem)))))
    (cond
     ((or test teste testn)
      (type-code :boolean
                   (append
                    (comp-args f args 2 :integer env)
                    (pop-regs 'a1)
                    (cond
                     (test (list (list (cdr test) ''a0 ''a1 ''a0)))
                     (teste (list '($sub 'a0 'a1 'a0) (list (cdr teste) ''a0 ''a0)))
                     (testn (list (list (cdr testn) ''a0 ''a1 ''a0) '($xori 'a0 'a0 1))))
                    (when tail '(($ret))))))
     (logical 
      (type-code :boolean
                 (append
                  (comp-args f args 2 :boolean env)
                  (pop-regs 'a1)
                  (list (list (cdr logical) ''a0 ''a0 ''a1))
                  (when tail '(($ret))))))
     (arith1
      (type-code :integer
                 (append
                  (comp-args f args 1 :integer env)
                  (list (list '$addi ''a0 ''a0 (cdr arith1)))
                  (when tail '(($ret))))))
     (arith
      (type-code :integer 
                 (append
                  (comp-args f args 2 :integer env)
                  (pop-regs 'a1)
                  (list (list (cdr arith) ''a0 ''a1 ''a0))
                  (when tail '(($ret))))))
     ((member f '(car cdr))
      (type-code :integer
                 (append
                  (comp-args f args 1 :integer env)
                  (if (eq f 'cdr) (list '($lw 'a0 4 '(a0)))
                    (list '($lw 'a0 0 '(a0)) '($lw 'a0 4 '(a0))))
                  (when tail '(($ret))))))
     (t ; function call
      (type-code :integer 
                 (append
                  (comp-args f args nil :integer env)
                  (when (> (length args) 1)
                    (append
                     (list (list '$mv (list 'quote (nth (1- (length args)) *params*)) ''a0))
                     (apply #'pop-regs (subseq *params* 0 (1- (length args))))))
                  (cond
                   (tail (list (list '$j f)))
                   (t (append
                       (apply #'push-regs (cons 'ra (reverse *used-params*)))
                       (list (list '$jal f))
                       (apply 'pop-regs (append *used-params* (list 'ra))))))))))))

(defun comp-args (fn args n type env)
  (unless (or (null n) (= (length args) n))
    (error "Incorrect number of arguments to '~a'" fn))
  (let ((n (length args)))
    (mappend #'(lambda (y)
                 (let ((c (comp y env nil)))
                   (decf n)
                   (checktype fn type (code-type c))
                   (if (zerop n) (code c) (append (code c) (push-regs 'a0)))))
             args)))
