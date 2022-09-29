;; *****************************
;; File: prover.lisp
;; Project: BoxFinder (Automated Theorem Prover)
;; Final Program: First-Order Predicate Logic Prover
;; Author: Blair Durkee
;; Date: 11/4/10
;; *****************************

(defvar inlist)
(defvar kb)
(defvar answer)
(defvar hash-copy)
(defvar kb_changed)
(defvar symtab)
(defvar use_symtab nil)

(defun remove_implies (l)
	(cond
		((or (not (listp l)) (eql l nil)) nil)
		(t (cond
			((eql (car l) 'implies)
				(setf (car l) 'or)
				(setf (second l) (list 'not (second l)))))
			(map nil #'remove_implies (cdr l)))))
					
(defun push_nots (l)
	(cond
		((or (not (listp l)) (eql l nil)) nil)
		(t
			(cond
				((and (eql (car l) 'not) (listp (second l)))
					(cond
						((eql (caadr l) 'not)
							(cond
								((listp (cadadr l))
									(setf (car l) (caadr (cadr l)))
									(setf (cdr l) (cdadr (cadr l))))
								(t
									(setf (car l) (cadadr l))
									(setf (cdr l) nil)))
							(push_nots l))
						((eql (caadr l) 'forall)
							(setf (car l) 'exists)
							(setf (cdr l) (cdadr l))
							(cons (list 'not) (caddr l))
							(setf (caddr l) (list 'not (caddr l)))
							(push_nots (third l)))
						((eql (caadr l) 'exists)
							(setf (car l) 'forall)
							(setf (cdr l) (cdadr l))
							(cons (list 'not) (caddr l))
							(setf (caddr l) (list 'not (caddr l)))
							(push_nots (third l)))
						((or (eql (caadr l) 'and) (eql (caadr l) 'or))
							(cond 
								((eql (caadr l) 'and)
									(setf (car l) 'or))
								((eql (caadr l) 'or)
									(setf (car l) 'and)))
							(setf (cdr l) (list (list 'not (second (cadr l))) (list 'not (third (cadr l)))))))))
			(map nil #'push_nots (cdr l)))))

(defun copy-hash-table (h)
	(setq hash-copy (make-hash-table :test #'equal :size 51))
	(maphash (lambda (k v) (setf (gethash k hash-copy) v)) h)
	hash-copy)
	
(defun get_skolem (h)
	(let ((l (list (gensym "S"))))
		(loop for v being the hash-values of h do
			(nconc l (list v)))
		l))
			
(defun standardize_vars (l h)
	(cond
		((or (not (listp l)) (null l)) nil)
		(t
			(cond
				((eql (car l) 'forall)
					(setq h (copy-hash-table h))
					(let ((new_sym (gensym "V")))
						(setf (gethash (string (second l)) h) new_sym)
						(set new_sym 'variable)
						(cond
							((eq (elt (string (second l)) 0) #\?)
								(setf (gethash (string-left-trim '(#\?) (string (second l))) h) new_sym))
							(t
								(setf (gethash (concatenate 'string "?" (string (second l))) h) new_sym)))
						(standardize_vars (third l) h)))
				((eql (car l) 'exists)
					(setq h (copy-hash-table h))
					(let ((new_skolem (get_skolem h)))
						(setf (gethash (string (second l)) h) new_skolem)
						(cond
								((eq (elt (string (second l)) 0) #\?)
									(setf (gethash (string-left-trim '(#\?) (string (second l))) h) new_skolem))
								(t
									(setf (gethash (concatenate 'string "?" (string (second l))) h) new_skolem)))
						(standardize_vars (third l) h)))
				(t
					(let ((free_sym 'predicate))
						(cond
							((not (or (eql (car l) 'and) (eql (car l) 'or) (eql (car l) 'not)))
								(set (car l) 'predicate)
								(setq free_sym 'constant)))
						(loop for i from 1 to (- (list-length l) 1) do 
							(cond
								((symbolp (nth i l))
									(cond
										((not (null (gethash (string (nth i l)) h)))
											(setf (nth i l) (gethash (string (nth i l)) h)))
										(t
											(set (nth i l) free_sym)))))))
					(map nil (lambda (x) (standardize_vars x h)) (cdr l)))))))
					
(defun drop_quantifiers (l)
	(cond
		((or (not (listp l)) (null l)) nil)
		(t
			(cond
				((or (eql (car l) 'forall) (eql (car l) 'exists))
					(setf (car l) (caaddr l))
					(setf (cdr l) (cdaddr l))
					(drop_quantifiers l))
				(t
					(map nil #'drop_quantifiers (cdr l)))))))
			
(defun distribute_ors (l)
	(cond
		((or (not (listp l)) (null l)) nil)
		(t
			(map nil #'distribute_ors (cdr l))
			(cond
				((eql (car l) 'or)
					(let ((left (cadr l)) (right (caddr l)))
						(cond
							((and (listp left) (eql (car left) 'and))
								(setf (car l) 'and)
								(let ((a (second left)) (b (third left)))
									(cond
										((and (listp right) (eql (car right) 'and))
											(let ((c (second right)) (d (third right)))
												(setf (cdr l) (list (list 'or a c) (list 'and (list 'or a d) (list 'and (list 'or b c) (list 'or b d)))))))
										(t
											(setf (cdr l) (list (list 'or a right) (list 'or b right)))))))
							((and (listp right) (eql (car right) 'and))
								(setf (car l) 'and)
								(let ((b (second right)) (c (third right)))
									(setf (cdr l) (list (list 'or left b) (list 'or left c))))))))))))

(defun unify (l1 l2)
	(cond
		((or (eql l1 l2) (and (symbolp l1) (symbolp l2) (eql (symbol-name l1) (symbol-name l2)))) t)
		((and (symbolp l1) (boundp l1) (eql (symbol-value l1) 'variable))
			(cond
				(use_symtab
					;(format t "adding symtab binding to ~A~%" l1)
					(setf (gethash l1 symtab) l2)))
			t)
		((and (symbolp l2) (boundp l2) (eql (symbol-value l2) 'variable))
			(cond
				(use_symtab
					;(format t "adding symtab binding to ~A~%" l2)
					(setf (gethash l2 symtab) l1)))
			t)
		((and (listp l1) (listp l2) (eql (list-length l1) (list-length l2)))
			(reduce (lambda (x y) (and x y))
				(map 'list #'unify l1 l2) :initial-value t))
		(t nil)))

(defun get_predicates (l)
	(cond
		((or (null l) (eql 'or l)) (list))
		((and (symbolp l) (eql (symbol-value l) 'predicate)) (list l))
		((listp l)
			(cond
				((eql (car l) 'not)
					(get_predicates (second l)))
				(t
					(append (get_predicates (car l)) (get_predicates (cdr l))))))))
					
(defun format_kb (l)
	(cond
		((or (null l) (eql 'or l)) (list))
		((symbolp l) (list l))
		((listp l)
			(cond
				((and (symbolp (car l)) (not (eql (car l) 'or)))
					(list l))
				(t
					(append (format_kb (car l)) (format_kb (cdr l))))))))

(defun store_in_kb (l)
	(cond
		((null l) nil)
		((not (listp l))
			(store_in_kb (list l)))
		((eql (car l) 'and)
			(map nil #'store_in_kb (cdr l)))
		(t
			(let ((ps (get_predicates l)) (found nil))
				(loop for p in ps do
					(cond
						((not found)
							(let ((cs (gethash p kb)))
								(setq l (format_kb l))
								(cond
									((null cs)
										(setq kb_changed t)
										(setf (gethash p kb) (list l)))
									(t
										(loop for c in cs do
											;(format t "checking unification of ~A and ~A~%" l c)
											(cond
												((unify l c)
													;(format t "~A is already in kb!~%~%" l)
													(setq found t))))
										(cond
											((not found)
												(setq kb_changed t)
												(nconc (gethash p kb) (list l))))))))))))))

(defun unify_union (l1 l2)
	(let ((result (list)) (d (append l1 l2)) (a) (matched))
		(loop while (not (null d)) do
			(setq matched nil)
			(setq a (car d))
			(setq d (cdr d))
			(dolist (e d)
				;(format t "unioning ~A to ~A~%" a e)
				(cond
					((unify a e)
						(setq matched t)
						(return))))
			(cond
				((not matched)
					(nconc result (list a)))))
		result))

(defun prove_kb ()
	(setq kb_changed nil)
	(maphash
		(lambda (k v)
			(cond ((and (not answer) (not kb_changed))
				(let ((new_c (list)) (canc (list)) (c1) (r v) (found nil))
					(loop while (and (not (null r)) (not kb_changed)) do
						(setq c1 (car r))
						(setq r (cdr r))
						(dolist (c2 r)
							;(format t "comparing ~A to ~A~%" c1 c2)
							(setq symtab (make-hash-table :size 51))
							(setq new_c (list))
							(setq canc (list))
							; look for contradictions
							(dolist (p1 c1)
								(dolist (p2 c2)
									(cond
										((and (listp p2) (eql (car p2) 'not) (unify p1 (second p2)))
											;(format t "found contradiction with ~A and ~A~%" p1 p2)
											(setq use_symtab t)
											(unify p1 (second p2))
											(setq use_symtab nil)
											(setq canc (union canc (list p1 p2))))
										((and (listp p1) (eql (car p1) 'not) (unify p2 (second p1)))
											;(format t "found contradiction with ~A and ~A~%" p1 p2)
											(setq use_symtab t)
											(unify p2 (second p1))
											(setq use_symtab nil)
											(setq canc (union canc (list p1 p2)))))))
							; add non-contradictory terms to a new clause
							(dolist (p (union c1 c2))
								(setq found nil)
								(dolist (np canc) do
									(cond ((unify p np)
										(setq use_symtab t)
										(unify p np)
										(setq use_symtab nil)
										(setq found t))))
								(cond ((not found)
									;(format t "adding ~A to new clause~%" p)
									(setq new_c (append new_c (list p))))))
							; if the new clause is unique, add it to the kb
							(cond
								((and (not (null canc)) (null new_c))
									;(format t "no new clause generated, setting to true~%")
									(setq answer t))
								((not (null canc))
									;(format t "applying symtab to: ~A~%" new_c)
									(maphash (lambda (k v) (setq new_c (subst v k new_c))) symtab)
									;(format t "adding new clause to kb: ~A~%" new_c)
									(store_in_kb new_c)))))))))
		kb)
		(cond (kb_changed
			;(format t "starting over!~%~%")
			(prove_kb))))

(defun convert_to_cnf (l)
	(remove_implies l)
	(push_nots l)
	(standardize_vars l (make-hash-table :test #'equal :size 51))
	(drop_quantifiers l)
	(distribute_ors l))
	
(defun print_kb ()
	(maphash (lambda (k v) (format t "~A:~%" k) (dolist (c v) (format t "  ~A~%" c))) kb))

(format t "Welcome to BoxFinder~%by Blair Durkee~%~%To input a theorem, enter a list of premises~%and a list of (negated) conclusions.~%~%")

(loop while t do
	(setq kb (make-hash-table :size 51))
	(setq answer nil)
	(loop for x in '("p" "c") do
		(format t "~A> " x)
		(finish-output nil)
		(setq inlist (read))
		(if (or (eql 'quit inlist) (and (listp inlist) (eql 'quit (car inlist)))) (quit))
		;(format t "Input: ~A~%" inlist)
		(loop for l in inlist do
			(convert_to_cnf l)
			(store_in_kb l)
			;(format t "CNF:   ~A~%" l)
			))
	;(format t "~%Knowledgebase:~%")
	;(print_kb)
	(prove_kb)
	(cond
		(answer
			(format t "~%TRUE~%~%"))
		(t
			(format t "~%FALSE~%~%"))))

