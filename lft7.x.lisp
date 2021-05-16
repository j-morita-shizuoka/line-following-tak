;Author: Junya Morita 
;Ver 2.00 May-15-2021
;
;;Change history
;Nov-5-2010 Change from character base environment to line base Environment
;Nov-18-2010 Add Keep-R, Keep-L, RtoS, LtoS  
;Nov-30-2010 Change reward methods
;Sep-16-2014 Include semi-MDP algorithms
;Jun-26-2017 Update to make the model compatible with ACT-R 7 environment
;May-15-2021 Update to make the model compatible with ACT-R 7.x environment

					;
;;Contents
;0. Global parameters
;1. Functions to create a device
; 1.1 Course
; 1.2 Trial
; 1.3 Block
; 1.4 Experiment
; 1.5 Result
;2. Model
; 2.1 ACT-R global parameters
; 2.2 Chunks
; 2.3 Rules
;  2.3.1 Perception
;  2.3.2 Motor Control
;   2.3.2.1 Manual mode
;   2.3.2.2 Auto mode
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;0. Global parameters;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar *show-responses* nil) ;Flag to create output file
(defvar *auto-capability* 10)  ;Success rates of the auto mode 
(defvar *manual-capability* 10)  ;Success rates of the manual mode
(defvar *prev-performance* 0)  ;Performance of the previous trial
(defvar *run-time* 1)   ;Time for one task session
(defvar *run-num* 0)   ;Counter of running
(defvar *disp-hi* 480)  ;Display height
(defvar *disp-wi* 640)  ;Display width
(defvar *keyable* nil) ;Key press counter
(defvar *course* nil) ;Course data
(defvar *interval-course* nil)  ;interval of the course character
(defvar *repeat-course* nil)  ;number of the course character within one period
(defvar *refresh* nil) ;Refresh rate of screen update
(defvar *vehicle-posi* nil) ;Circle position
(defvar *vehicle-x-posi* nil) ;Circle position
(defvar *vehicle-y-posi* nil) ;Circle position
(defvar *vehicle-size* nil)  ;
(defvar *vehicle-radius* nil)  ;
(defvar *subseq-course* 320) ;Circle position
(defvar *auto* nil) ;If the value is 1, the auto is selected. otherwise the manual is selected.
(defvar *course-length* 100) ;Course length
(defvar *window* nil)
(defvar *vehicle* nil)
(defvar *debg* nil)
(defvar *key* nil)
(defvar *line-posi* nil)
(defvar *self-conf* nil)
(defvar *trust* nil)
(defvar *thresh* nil)
(defvar *move-distance* 0)
(defvar *sync* nil)
(defvar *real-time* nil)

;copied from extended-motor-module test
(defparameter *kct* .01)
(defparameter *krt* .04)
(defparameter *dp* nil)
(defparameter *de* t)
(defparameter *psd* nil)
(defparameter *cdd* nil)
(defparameter *dpd* .075)
(defparameter *fpd* .05)
(defparameter *spd* .1)
                       
(defvar *data* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;1. Functions to create a device;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;1.1 Course;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Create-random-course outputs a number sequence ranging from -2 to 2 such as (0 1 1 -2...-1) 
;in which -2, -1, 0, 1, 2 indicate sharp left, left, straight, right, sharp right respectively.
;The Numbers are randomly assigned unless the course run out the display
(defun create-random-course (number-course)
  (let ((course-list nil) 
	(current-posi 320) 
	(ran nil) 
	(next-posi nil))
    (dotimes (i number-course)
      (setf ran (- (random 5) 2))
      (setf next-posi (+ (* ran (* *interval-course* *repeat-course*)) current-posi))
      (if (or (> next-posi *disp-wi*) (< next-posi 0))
	  (setf ran (* ran -1)))
      (push ran course-list)
      (setf current-posi (+ (* ran (* *interval-course* *repeat-course*)) current-posi)))
    (reverse course-list)))

;Prepare-next adds subgoals to the number sequence output by "create-random-course". 
;ex. ((0 N) (1 L) (1 L)...(-2 R))
;Sub goals are displayed as "S" on the window though the participant couldn't observe it in the experiment.
;The model and the automation system are heading to the nearest subgoal.
(defun prepare-next (i res pattern)
  (let ((pat1 (car pattern)) (pat2 (nth i pattern)))
    (if pat1
	(if pat2
	    (if (equal 0 (* pat1 pat2))
		(if (equal 0 (+ pat1 pat2))
		    (prepare-next (+ i 1) res pattern)
		    (if (equal pat2 0)
			(prepare-next (+ i 1) res pattern)
			(prepare-next 1 (proceed-until-next i res (judge-dir pat2))
				     (nthcdr i pattern))))
		(prepare-next 1 (append res (list (list pat1 (judge-dir pat1))))
			     (cdr pattern)))
	    (proceed-until-next i res (second (car res))))
	res)))

(defun judge-dir (pat2)
  (if (> pat2 0) 'R 'L))

(defun proceed-until-next (i res dir)
  (if (equal i 0)
      res
      (proceed-until-next (- i 1) (append res (list (list 0 dir))) dir)))

;Create-course transforms the number sequence output by prepare-next to screen positions.
(defun create-course (pattern)
  (let ((result (list (list 320))) (dir 'nu) pat1)
    (dotimes (i (length pattern))
      (setf pat1 (car (nth i pattern)))
      (if (nth (+ i 1) pattern)
	  (setf dir (second (nth (+ i 1) pattern))))
      (setf result (repeat-pattern-course result (* pat1 *interval-course*) dir)))
    (reverse result)))

(defun repeat-pattern-course (result num dir)
  (dotimes (i *repeat-course*)
    (let ((posi (+ (car (car result)) num)))
      (if dir
	(if (equal i (- *repeat-course* 1))
	      (push (list posi dir) result)
	      (push (list posi) result))
	  (push (list posi) result))))
    result)


;;1.2 Trial;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Trial is defined as a screen update.
;do-trial prepares the window for the task.
;the window is presented to the model for the duration defined as *refresh*.
(defun do-trial (course)  
  (let* ((subgoal nil)
	 ;(*line-posi* (return-line-posi course))
	 (*subseq-course* (subseq course 0 *repeat-course*)))
					;draw course
    ;(format t "tes")
    (clear-exp-window)
    (setf subgoal (draw-course course))
    (setf *vehicle-x-posi* (+ *vehicle-posi* *vehicle-radius*))
    ;(setf (x-pos vehicle) *vehicle-x-posi*) 
    (if (equal *prev-performance* 0)
	    (add-text-to-exp-window 
	     *window* "'" :width 1 :color 'RED :x *vehicle-x-posi* :y *vehicle-y-posi*)
	    
	    (add-text-to-exp-window 
	     *window* "'" :width 1 :color 'GREEN :x *vehicle-x-posi* :y *vehicle-y-posi*))

    ;(add-items-to-exp-window vehicle)
    (when *debg*
	;(draw-vehicle *vehicle-x-posi* *vehicle-y-posi* *vehicle-radius* 0 (+ (* -2 *vehicle-radius*) 3))
	(when (equal *prev-performance* 1) (show-error-line)))	
    (setf *keyable* t)
    (if *auto* 
	(auto-exe (car (last subgoal)))
	(manual-exe (car (last subgoal))))
    ;output results to a file.
    (send-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
    (setf *prev-performance* 
	  (collision-detection-cl *subseq-course* 
				  (* *vehicle-radius* *vehicle-radius*) *vehicle-x-posi* *disp-hi*))))

(defun draw-vehicle (vehicle-x-posi vehicle-y-posi x y f)
  (when (>= x y)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi)
			    (list (+ vehicle-x-posi x) (+ vehicle-y-posi y)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi)
			    (list (- vehicle-x-posi x) (+ vehicle-y-posi y)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (+ vehicle-x-posi x) (- vehicle-y-posi y)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (- vehicle-x-posi x) (- vehicle-y-posi y)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (+ vehicle-x-posi y) (+ vehicle-y-posi x)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (- vehicle-x-posi y) (+ vehicle-y-posi x)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (+ vehicle-x-posi y) (- vehicle-y-posi x)) 'light-gray)
    (add-line-to-exp-window *window* (list vehicle-x-posi vehicle-y-posi) 
			    (list (- vehicle-x-posi y) (- vehicle-y-posi x)) 'light-gray)
    (when (>= f 0 )
      (setf x (- x 1))
      (setf f (- f (* 4 x))))
    (draw-vehicle vehicle-x-posi vehicle-y-posi x (+ y 1) (+ f (+ (* 4 y) 2)))))


;the following six functions are sub-functions of do-trial.
(defun draw-course (course)
  (let ((subgoal nil) (yposi *disp-hi*) (subg) (txt-c) (offset 2) (xposi) (next) (flag nil)
	(courseg (remove-if-not #'(lambda (x) (second x)) course))
	(ixposi (car (car course))))  
    (dotimes (i (length course))
      (setf yposi (- yposi *interval-course*))
      (setf xposi (car (nth i course)))
      (setf subg (second (nth i course)))
      (if *auto* 
	  (progn
	    ;(setf offset 2)
	    (setf txt-c 'blue))
	  (progn
	    ;(setf offset (* *vehicle-radius* -1))
	    (setf txt-c 'yellow)))
      (if (equal yposi (- *vehicle-y-posi* 10))
	  (add-text-to-exp-window 
	   *window* "." :width 1 :x xposi :y yposi :color 'cyan))
      (when subg
	(setf courseg (cdr courseg))
	(if (car (nth (+ i 1) course))
	    (setf next (car (nth (+ i 1) course)))
	    (setf next 0))
	(when *debg*
	  (if (car courseg)
	      (when (< (+ i 1) (length course))
		(if (<= i 50)
		    (add-line-to-exp-window *window* (list xposi yposi)
					    (list ixposi *disp-hi*) 'black))
		(add-line-to-exp-window *window* (list (car (car courseg)) (- yposi 50))
					(list xposi yposi) 'black))
	      (add-line-to-exp-window *window* (list xposi yposi)
				      (list (car (car (reverse course))) 1) 'black)))
	(when  (and (<= yposi (- *vehicle-y-posi* (* (abs (- xposi next)) 3))) ;nearest goal
		    (>= yposi (- *vehicle-y-posi* 100))
		    (null flag))
	  (setf flag 1)
	  (if (equal subg 'L)
	      (progn
		(push (- xposi *vehicle-radius*) subgoal)
		(add-text-to-exp-window 
		 *window* "G" :width 1 :x (- xposi (+ *vehicle-radius* offset)) :y yposi :color txt-c))
	      (progn
		(push (+ xposi *vehicle-radius*) subgoal)	      
		(add-text-to-exp-window 
		 *window* "G" :width 1 :x (+ xposi (+ *vehicle-radius* offset)) :y yposi :color txt-c))))))
					;(add-text-to-exp-window :text "." :width 140 :x xposi :y yposi)
    ;chunk representing distance between the vehicle and the line may be needed
    subgoal))

(defun goal-posi (xposi next)
  (if next
      (if (equal (abs (- next xposi)) 0)
	  0
	  (if (equal (abs (- next xposi)) 1)
	      8
	      (if (equal (abs (- next xposi)) 2)
		  10))))
  0)

(defun return-line-posi (course)
  (let ((line-posi nil) (yposi *disp-hi*) (xposi))  
    (dotimes (i (length course))
      (setf yposi (- yposi *interval-course*))
      (setf xposi (car (nth i course)))
      (when (= yposi *vehicle-y-posi*)
	(setf line-posi xposi)))
    line-posi))

(defun show-error-character ()
  (dotimes (i 50)
    (let ((pos (* i 10)))
      (add-text-to-exp-window *window* "O" :x pos :y 0 :color 'YELLOW)
      (add-text-to-exp-window 
       *window*  "O" :x pos :y (- *disp-hi* 10) :color 'YELLOW)
      (add-text-to-exp-window *window* "O" :x 0 :y pos :color 'YELLOW)
      (add-text-to-exp-window *window* "O" :x 490 :y pos :color 'YELLOW))))

(defun show-error-line ()
  (add-line-to-exp-window *window* (list 5 (- *disp-hi* 5)) (list 5 5) 'light-gray)
  (add-line-to-exp-window *window* (list (- *disp-wi* 5) 5)  (list 5 5) 'light-gray)
  (add-line-to-exp-window *window* (list (- *disp-wi* 5)  (- *disp-hi* 5))  (list (- *disp-wi* 5) 5) 'light-gray)
  (add-line-to-exp-window *window* (list 5 (- *disp-hi* 0))  (list (- *disp-wi* 5)  (- *disp-hi* 0)) 'light-gray))



;collision detection
(defun collision-detection (answer)
  (if (and (<= *vehicle-posi* answer) 
	   (<= answer (+ *vehicle-posi* *vehicle-size*)))
      (progn
	(setf *prev-performance* 0)
	0)
      (progn
	(setf *prev-performance* 1)
	(if (> answer *vehicle-posi*)
	    (- answer *vehicle-posi*)
	    (abs (- (+ *vehicle-posi* *vehicle-size*) answer))))))

(defun collision-detection2 (ve line)
  (if (and (<= ve line) (<= line (+ ve *vehicle-size*))) 0 1))


;collistion detection between circle and line
(defun collision-detection-cl (course vehicle-radius-sq vxposi yposi)
  (if (or (null course) (not (listp course)))
      1
      (let* ((xposi (car (car course)))
	     (xdis (- xposi vxposi))
	     (ydis (- yposi *vehicle-y-posi*))
	     (dis (+ (* xdis xdis) (* ydis ydis))))
	(if (<= (- dis 4) vehicle-radius-sq)
	    0
	    (collision-detection-cl (cdr course) 
				    vehicle-radius-sq vxposi 
				    (- yposi *interval-course*))))))
     
;key press
(defun key-down-recorder (model key)
  (declare (ignore model))
  (when *keyable*
    (setf *keyable* nil)
    (if (equal (string key) "j")
	(setf *key* 'left)
	(if (equal (string key) "l")
	    (setf *key* 'right)
	    (if (null *auto*)
	;(if (equal (string key) " ")
		(progn
		  (setf *auto* 1)
		  (setf *key* 'straight));)
	;(when (equal (string key) " ")
		(progn
		  (setf *auto* nil)
		  (setf *key* 'straight))))))
  (push-last (list :pressed (mp-time) key) *data*))

(defmethod key-up-recorder (model key)
  (declare (ignore model))
  (when *keyable*
    (setf *keyable* nil)
    (when (equal (string key) "j")
      (setf *key* 'straight))
    (when (equal (string key) "l")
      (setf *key* 'straight)))
  (push-last (list :released (mp-time) key) *data*))

(defun setup-monitors ()
  (add-act-r-command "extended-motor-key-down" 'key-down-recorder
		     "Monitor for output-key in testing extended-motor-actions extra.")
  (monitor-act-r-command "output-key" "extended-motor-key-down")
  (add-act-r-command "extended-motor-key-up" 'key-up-recorder
		     "Monitor for release-key in testing extended-motor-actions extra.")
  (monitor-act-r-command "release-key" "extended-motor-key-up"))

(defun remove-monitors ()
  (remove-act-r-command-monitor "output-key" "extended-motor-key-down")
  (remove-act-r-command-monitor "release-key" "extended-motor-key-up")
  (remove-act-r-command  "extended-motor-key-down")
  (remove-act-r-command  "extended-motor-key-up"))


(defun manual-exe (subgoal)
  (let ((prev *vehicle-posi*))
    (if *key*
	(unless (or (equal *key* 'straight) (equal subgoal *vehicle-x-posi*))
	  (dotimes (i 2)
	    (when (> *manual-capability* (act-r-random 10))   
	      (when (and (equal *key* 'left) 
			 (> *vehicle-posi* *interval-course*))
		(increment-posi (- *vehicle-posi* *interval-course*)))
		;(setf *vehicle-posi* (- *vehicle-posi* *interval-course*)))
	      (when (and (equal *key* 'right) 
			 (< *vehicle-posi* (- *disp-wi* *vehicle-radius*)))
		(increment-posi (+ *vehicle-posi* *interval-course*)))))
      (setf *move-distance* (/ (abs (- prev *vehicle-posi*)) *interval-course*))))))

;auto mode
(defun auto-exe (subgoal)
  (let ((prev *vehicle-posi*) 
	;(v2 (* *vehicle-radius* *vehicle-radius*))
	g)	
    (if (equal *prev-performance* 1)
	(setf g (return-line-posi *subseq-course*))
	(setf g subgoal))	
    (unless (and (equal subgoal *vehicle-x-posi*)
		 (equal *prev-performance* 0))
      (dotimes (i 2)
	(when (> *auto-capability* (act-r-random 10))
	  (if (> g *vehicle-x-posi*)
	      (increment-posi (+ *vehicle-posi* *interval-course*))
	      (increment-posi (- *vehicle-posi* *interval-course*)))))
      ;(unless (equal 'press-space (chunk-slot-value-fct (act-r-buffer-chunk (buffer-instance 'goal)) 'previous-rule))
	;(trigger-reward (/ (abs (- prev *vehicle-posi*)) *interval-course*)))))
      (setf *move-distance* (/ (abs (- prev *vehicle-posi*)) *interval-course*)))))

;This function stabilizes the vehicle movement.
(defun increment-posi (current)
  (if (or (not (and 
		(equal (collision-detection-cl 
			*subseq-course*					      
			(* *vehicle-radius* *vehicle-radius*) 
			*vehicle-x-posi* 
			*disp-hi*)
		       0)
		(equal (collision-detection-cl 
			*subseq-course* 
			(* *vehicle-radius* *vehicle-radius*)
			(+ current *vehicle-radius*) 
			*disp-hi*) 
		       1)))
	  (equal *prev-performance* 1))
    (setf *vehicle-posi* current)))



;;1.3 Block;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Block is defined as a trial sequence in which the same auto/manual capabilities are used.
(defun run-block (ac mc file)
  (setf *auto-capability* ac) 
  (setf *manual-capability* mc)
;  (setf *window*
;	(open-exp-window "Line Tracing Task" 
;			 :visible *debg* ;if :visible is nil, the display isn't shown and the model runs fast.
;			 :width *disp-wi* 
					;			 :height *disp-hi*))
  (setf *window*
	  (open-exp-window "Line Tracing Task" 
			   :visible *debg* ;if :visible is nil, the display isn't shown and the model runs fast.
			 :width *disp-wi* 
			 :height *disp-hi*))
  (install-device *window*)
  (add-text-to-exp-window 
   *window* "'" :width 1 :color 'RED :x *vehicle-x-posi* :y *vehicle-y-posi*)
  (setf *key* 'straight)
  (set-hand-location right 15 6)
  (set-hand-location left 7 6)
  (setup-monitors)  
  (schedule-periodic-event 
   *refresh* 'update-curse :maintenance t)
  (run 20  *real-time*)
  (remove-monitors))
  
(defun update-curse ()
  (do-trial (subseq *course* 0 (/ *disp-hi* *interval-course*)))
  (setf *course* (cdr *course*)))


;run without the visible window
(defun run-block-init (ac mc)
  (init)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (reset) ;initialize
  (pdisable to.auto2)	      
  (pdisable to.manual2)
  (setf *run-time* 0) 
  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
  (run-block ac mc (format nil "~A/output.txt" (user-homedir-pathname))))

;run with the visible window
(defun run-block-debg (ac mc)
  (init)
  (setf *debg* t)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (reset) ;initialize
  (pdisable to.auto2)	      
  (pdisable to.manual2)
  (pdisable find.v.online2)
  (pdisable find.v.ongoal2)
  (pdisable find.v.nega)
  (setf *run-time* 0)
  (setf *real-time* t)
  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course (round (/ *course-length* 4))))))
  (run-block ac mc (format nil "~A/output.txt" (user-homedir-pathname))))
      

;;1.4 Experiment;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Experiment is defined as a block sequence in which the auto/manual capabilities are varied.

;run-experimen corresponds Experiment 2 that manupulates Ca/Cm.
(defun run-experiment (n)
  (init)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (dotimes (k n)
    (setf *run-num* k)
    (dotimes (i 5)
      (dotimes (j 5)
	(reset) ;initialize
	(setf *run-time* 0) 
	(pdisable to.auto2)	      
	(pdisable to.manual2)
	(if (equal (act-r-random 2) 1)
	    (setf *auto* 1)
	    (setf *auto* nil))
	(setf *vehicle-posi* 320)
	(setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
	(run-block (+ i 3) (+ j 3) (format nil "~A/output.txt" (user-homedir-pathname)))))))


(defun combine-capabilities (list1 output)
  (dolist (l1 list1)
    (dolist (l2 list1)
      (push (list l1 l2) output)))
  output)

(defun random-order (list output)
  (if list
      (let ((x1 (nth (random (length list)) list)))
	(random-order (remove x1 list) (push x1 output)))
      output))

;run-experiment-single-mode corresponds Experiment 1 that examines baseline performance.
;mode can be selected from "auto" or "manual"
(defun run-experiment-single-mode (n mode)
  (init)
  (setf *debg* nil)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (dotimes (k n)
    (setf *run-num* k)
    (dotimes (j 5)
      (reset) ;initialize
      (setf *run-time* 0) 
      (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
      (setf *vehicle-posi* (- 320 (/ *vehicle-size* 2)))
      (if (equal mode "auto")
	  (progn
	    (pdisable find.v.through) 
	    (pdisable find.v.online) 
	    (pdisable find.v.ongoal) 
	    (pdisable find.v.online2) 
	    (pdisable find.v.ongoal2) 
	    (pdisable find.v.move) 
	    (pdisable find.v.nega) 
	    (pdisable find.goal)
	    (pdisable keep.m)
	    (pdisable to.manual) 
	    (pdisable to.manual2) 
	    (setf *auto* 1)
	    (run-block (+ j 3) 3 (format nil "~A/output.txt" (user-homedir-pathname))))
	  (progn
	    (pdisable to.auto)
	    (pdisable to.auto2)
	    (setf *auto* nil)
	    (run-block 3 (+ j 3) (format nil "~A/output.txt" (user-homedir-pathname))))))))

(defun run-block-single-mode (j mode)
  (init)
  (setf *debg* t)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (reset) ;initialize
  (setf *run-time* 0) 
  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
  (setf *vehicle-posi* (- 320 (/ *vehicle-size* 2)))
  (if (equal mode "auto")
      (progn
	(pdisable find.v.through) 
	(pdisable find.v.online)
	(pdisable find.v.ongoal)
	(pdisable find.v.online2)
	(pdisable find.v.ongoal2)
	(pdisable find.v.move) 
	(pdisable find.v.nega) 
	(pdisable find.goal)
	(pdisable keep.m)
	(pdisable to.manual) 
	(pdisable to.manual2) 
	(setf *auto* 1)
	(run-block j 3 (format nil "~A/output.txt" (user-homedir-pathname))))
      (progn
	(pdisable to.auto)
	(pdisable to.auto2)
	(setf *auto* nil)
	(run-block 3 j (format nil "~A/output.txt" (user-homedir-pathname))))))

(defun run-block-single-mode-dbg (j mode)
  (init)
  (prepare-output-file (format nil "~A/output.txt" (user-homedir-pathname)))
  (reset) ;initialize
  (setf *run-time* 0) 
  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
  (setf *vehicle-posi* (- 320 (/ *vehicle-size* 2)))
  (if (equal mode "auto")
      (progn
	(pdisable find.v.through) 
	(pdisable find.v.online)
	(pdisable find.v.ongoal)
	(pdisable find.v.online2)
	(pdisable find.v.ongoal2)
	(pdisable find.v.move) 
	(pdisable find.v.nega) 
	(pdisable find.goal)
	(pdisable keep.m)
	(pdisable to.manual) 
	(pdisable to.manual2) 
	(setf *auto* 1)
	(run-block-debg j 3))
      (progn
	(pdisable to.auto)
	(pdisable to.auto2)
	(setf *auto* nil)
	(run-block-debg 3 j))))

;manipulate-alpha-egs
(defun run-experiment-alpha-egs (n a e th)
  (init)
  (let ((file (format nil "~A/manip/output~A~A~A.txt" (user-homedir-pathname) a e th)))
    (prepare-output-file file)
    (dotimes (k n)
      (setf *run-num* k)
      (dotimes (i 5)
	(dotimes (j 5)
	  (reset) ;initialize
	  (setf *run-time* 0) 
	  (set-sgp (* (+ a 1) 0.05) (* e 0.5))
	  (if (equal (act-r-random 2) 1)
	      (setf *auto* 1)
	      (setf *auto* nil))
	  (setf *vehicle-posi* 320)
	  (if (equal th 1)
	      (progn
		(pdisable to.auto)
		(pdisable to.manual))
	      (progn
		(pdisable to.auto2)	      
		(pdisable to.manual2)))
	  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
	  (run-block (+ i 3) (+ j 3) file))))))

(defun run-experiment-s-m-r (n &key (s 1) (m 1) (r 1))
  (init)
  (let ((file (format nil "~A/manip/output~A~A~A.txt" (user-homedir-pathname) s m r)))
    (prepare-output-file file)
    (dotimes (k n)
      (setf *run-num* k)
      (dotimes (i 5)
	(dotimes (j 5)
	  (reset) ;initialize
	  (setf *run-time* 0) 
	  ;(set-sgp (* (+ a 1) 0.05) (* e 0.5))
	  (if (equal (act-r-random 2) 1)
	      (setf *auto* 1)
	      (setf *auto* nil))
	  (setf *vehicle-posi* 320)
	  (if (equal s 1)
	      (setf *sync* t)
	      (setf *sync* nil))
	  (if (equal m 1)
	      (progn
		(pdisable to.auto2)
		(pdisable to.manual2))
	      (progn
		(pdisable to.auto)	      
		(pdisable to.manual)))
	  (if (equal r 1)
	      (progn
		(pdisable find.v.nega)
		(pdisable find.v.online2)
		(pdisable find.v.ongoal2))
	      (progn
		(pdisable find.v.online)
		(pdisable find.v.ongoal)
		(pdisable find.v.move)))
	  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
	  (run-block (+ i 3) (+ j 3) file))))))

(defun manipulate-alpha-egs ()
  (dotimes (a 4)
    (dotimes (e 4)  
      (run-experiment-alpha-egs 30 a e 0)))
  (dotimes (a 4)
    (dotimes (e 4)  
      (run-experiment-alpha-egs 30 a e 1))))

(defun manipulate-alpha-egs2 (th)
  (dotimes (a 4)
    (dotimes (e 4)  
      (run-experiment-alpha-egs 30 a e th))))

;manipulate threshold
(defun run-experiment-thresh-egs (n e th)
  (init)
  (let ((file (format nil "~A/manip/output~A~A~A.txt" (user-homedir-pathname) 0 e th)))
    (prepare-output-file file)
    (dotimes (k n)
      (setf *run-num* k)
      (dotimes (i 5)
	(dotimes (j 5)
	  (reset) ;initialize
	  (setf *run-time* 0) 
	  (setf *thresh* e)
	  (if (equal (act-r-random 2) 1)
	      (setf *auto* 1)
	      (setf *auto* nil))
	  (setf *vehicle-posi* 320)
	  (if (equal th 1)
	      (progn
		(pdisable to.auto)
		(pdisable to.manual))
	      (progn
		(pdisable to.auto2)	      
		(pdisable to.manual2)))
	  (setf *course* (create-course (prepare-next 1 '((0 R)) (create-random-course *course-length*))))
	  (run-block (+ i 3) (+ j 3) file))))))


(defun set-sgp (al eg)
  (let ((al (float al)) (eg (float eg)))
    `(sgp-fct '(:alpha ,al :egs ,eg))))


  
(defun init ()
  (setf *move-distance* 0)
  (setf *self-conf* 0)
  (setf *trust* 0)
;  (setf *thresh* (/ 1 3))
  (setf *thresh* 0)
  (setf *prev-performance* 0)
  (setf *run-num* 1)
  (setf *debg* nil)
  (setf *key* 'straight)
  (setf *disp-hi* 480)
  (setf *vehicle-size* 24)  ;Original is 24 px
  (setf *vehicle-posi* (- 320 (/ *vehicle-size* 2)))  
  (setf *interval-course* 1) ;Original is 1px
  (setf *repeat-course* (floor (/ 50 *interval-course*))) ;The length of course parts in the original is 48
  (setf *refresh* (float (/ 2 *repeat-course*))) ;The couse parts passes at 2 sec in the original 
  ;(setf *refresh* 0.2) ;The couse parts passes at 2 sec in the original 
  (setf *course-length* (* *repeat-course* 21)) ;One block lasts 40 seconds that contains 20 parts blocks
  (setf *vehicle-radius* (/ *vehicle-size* 2))
  (setf *vehicle-y-posi* (- *disp-hi* 40))
  (setf *vehicle-x-posi* (+ *vehicle-posi* *vehicle-radius*))
  (if (equal (act-r-random 2) 1)
      (setf *auto* 1)
      (setf *auto* nil)))



;;1.5 Result;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;These are functions to suGmmarize data.
;Output score, auto use ratio, and utilities.

(defun prepare-output-file (file)
  (let ((output-stream 
	  (open file
		:direction :output :if-exists :supersede)))
    (format output-stream 
	    "Rn Ca Cm Auto OnLine")
    (dolist (st '(keep.a keep.m l.to.s r.to.s to.left to.right)) (format output-stream " ~S " st))
    (close output-stream)))

(defmacro spp-temp (name value)
  ;(let ((value (intern (format nil "~S" *self-conf*))))
  ;(let ((value *self-conf*))
  ;(let ((value 10))
  `(spp ,name :u ,value))


(defun ex-dif (lis num)
  (if (second lis)
      (if (equal (car lis)
		 (second lis))
	  (ex-dif (cdr lis) (+ num 1))
	  (if (nth 2 lis)
	      (if (equal (second lis)
			 (nth 2 lis))
		  num
		  (+ num 1))
	      (+ num 1)))
      nil))

;send-output-file is used in do-trial to print results of each trial.
(defun send-output-file (file)
  (let ((output-stream 
	 (open file
	       :direction :output :if-exists :append))
	(auto-manual)
	(man-p '(keep.a keep.m l.to.s r.to.s to.left to.right))
	(uvalue (mapcar #' car (no-output (spp-fct '((keep.a keep.m l.to.s r.to.s to.left to.right) :u))))))
    (if (ex-dif (cdr uvalue) 0)
	(if *sync*
	    (progn
	      (setf *self-conf* (nth (ex-dif (cdr uvalue) 0) (cdr uvalue)))
	      (setf (production-u 'keep.m) *self-conf*)
	      (setf (production-u 'to.left) *self-conf*)
	      (setf (production-u 'to.right) *self-conf*)
	      (setf (production-u 'l.to.s) *self-conf*)
	      (setf (production-u 'r.to.s) *self-conf*)
	      )
	    (setf *self-conf* (second uvalue)))
	(setf *self-conf* (second uvalue)))
    (if (nth (position 'keep.a man-p) uvalue)
	(setf *trust* (nth (position 'keep.a man-p) uvalue)))
    (if *auto*
	(setf auto-manual 1)
	(setf auto-manual 0))
    (format output-stream
	    "~%~S ~S ~S ~S ~S" 
	    *run-num* *auto-capability* *manual-capability* auto-manual (- 1 *prev-performance*))
    (dolist (st uvalue) (format output-stream " ~S " st))
    (close output-stream)))


(defun return-trust ()
  (let ((man-p '(keep.a keep.m l.to.s r.to.s to.left to.right))
	(uvalue (mapcar #' car (no-output (spp-fct '((keep.a keep.m l.to.s r.to.s to.left to.right) :u))))))
    (nth (position 'keep.a man-p) uvalue)))

(defun return-conf ()
  (let ((man-p '(keep.a keep.m l.to.s r.to.s to.left to.right))
	(uvalue (mapcar #' car (no-output (spp-fct '((keep.a keep.m l.to.s r.to.s to.left to.right) :u))))))
    (nth (position 'keep.m man-p) uvalue)))

;;Functions used in the model
(defun return-current-key-state ()
  (if *key*
      (format nil "~A" *key*)))

(defun return-current-mode ()
  (if *auto* 
      "A"
      "M"))

(defun wait-a()
  (if (equal 'press-space (chunk-slot-value-fct (act-r-buffer-chunk (buffer-instance 'goal)) 'previous-rule))
      (null *auto*)
      1))

(defun wait-m()
  (if (equal 'press-space-a (chunk-slot-value-fct (act-r-buffer-chunk (buffer-instance 'goal)) 'previous-rule))
      *auto*
      1))

(defun calc-delay(tim out)
  (if (eq tim 0)
      (+ out 0.011)
      (calc-delay (- tim 1) (+ out (* 0.011 (expt 1.1 tim))))))

(defun utility-test(producction a b)
  10)


;;2 Model;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(clear-all)
(require-extra "extended-motor-actions")


(define-model line-trace

;;2.1 ACT-R global parameters;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(sgp 
 :v t ;send model output to the *standard-output* stream (slow).
 ;:v "tracedri.txt" ;send model output to file (faster).
 :esc t ;enable subsymbolic computation parameter. 
 :ul t ;utility learning.
 ;:alpha  .01
 ;:egs 1 ;It specifies the s parameter for the noise added to the utility values.
 ;:reward-hook utility-test
 :show-focus nil ;This indicates where the model's visual attention is located.
 :needs-mouse nil ;Don't use mouse.
; :trace-detail high ;trace detail is selected from "low", "medium" and "high"
 ;:buffer-trace t
 ;:buffer-trace-step .025
 ;:traced-buffers (visual-location manual production goal temporal)
 ;:traced-buffers (visual-location manual production)
 ) 
;(sgp :seed (100 0))

;    (sgp-fct (list :v t :key-closure-time *kct* 
;                   :needs-mouse t :cursor-drag-delay *cdd*
;                   :key-release-time *krt* :dual-processor-stages *dp*
;                   :dual-execution-stages *de* :peck-strike-distance *psd*
;                   :default-punch-delay *dpd* :fast-punch-delay *fpd*
;                   :slow-punch-delay *spd*))


;;2.2 Chunks;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;chunk for goal buffer
(chunk-type  
 move-vehicle 
 previous-rule ;store previously used rule (If switch modes are fired, it doesnot fire at next trial)
 next-reward 
 prev-vehicle-loc ;store current-vehicle position
 prev-goal-loc ;store current-vehicle position
 vehicle-loc ;store current-vehicle position
 goal-loc ;store horizontal position of attended goal
 current-mode  ;store current mode ("M" or "A")
 trust
 self-conf
 ) 

(chunk-type mode lab key) 
;(chunk-type manual lab key)
(chunk-type press-space)
(chunk-type press-space-a)
(chunk-type press-space-m)
(chunk-type keep-dir)

(add-dm
 ;(auto isa mode lab "A" key "space")
 (manual isa mode lab "A" key "space")
 (sucess isa chunk)
 (failure isa chunk)
 (press-space isa chunk)
 (press-space-a isa chunk)
 (press-space-m isa chunk)
 (auto isa chunk)
 (keep-dir isa chunk)
 (goal isa move-vehicle))

;;2.3 Rules;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;2.3.1 Perception;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;IF current vehicle location is NIL and visual there is a red object in the VL-buffer, 
;;THEN place the visual location in G-buffer, and place next goal position in the VL-buffer.

;no reward
;after mode changing, no rewards are given to the model
(p find.v.through
   =goal>
     isa      move-vehicle
     next-reward nil
     vehicle-loc nil
   =visual-location>
     isa      visual-location
     - color    black ;color other than red or green
     - color    light-gray
     - color    blue
     - color    yellow
     - color    cyan
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red ;vehcle
     - color    green ;vehcle
     - color    black ;line
     - color    light-gray ;misc
     - color    cyan ;marker
     ;- color    yellow ;goal
     ;value text
   +temporal>
     isa time 
)

(p find.v.f
   =goal>
     isa      move-vehicle
     next-reward nil
     vehicle-loc nil
   =visual-location>
     isa      visual-location
     - color    red
     - color    green
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    black ;line
     - color    light-gray ;misc
     - color    cyan ;marker
     - color    yellow ;goal
     ;value text
   +temporal>
     isa time 
)



;when the vehicle is on the line, max rewards are given to the model
(p find.v.online
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     ;prev-goal-loc =posi2
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     color    red ;the vehicle is on the line
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    ;execution free
   =temporal>
    isa time
    ticks =tim
   ;!eval! (trigger-reward (* 48 (calc-delay =tim 0)))
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
     ;changed for manipulating dynamics
     next-reward nil
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
   +temporal>
     isa time 
   ;!output! =tim
   !eval! (trigger-reward (* 48 (calc-delay =tim 0)))
)

(p find.v.online2
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     ;prev-goal-loc =posi2
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     color    red ;the vehicle is on the line
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    ;execution free
   =temporal>
    isa time
    ticks =tim
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
     ;changed for manipulating dynamics
     next-reward nil
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
   +temporal>
     isa time 
   ;!output! =tim
)

;when the vehicle is on the same x position as the goal, max rewards are given to the model

(p find.v.ongoal
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     prev-goal-loc =posi1
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     ;color    red
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    ;execution free
   =temporal>
    isa time
    ticks =tim
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
     ;changed for manipulating dynamics
     next-reward nil
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
   +temporal>
     isa time 
   !eval! (trigger-reward (* 48 (calc-delay =tim 0)))
)

(p find.v.ongoal2
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     prev-goal-loc =posi1
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     ;color    red
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
  ?manual>      
    preparation free
    processor free
    ;execution free
   =temporal>
    isa time
    ticks =tim
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
     ;changed for manipulating dynamics
     next-reward nil
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
   +temporal>
     isa time 
)

;when the vehicle is off the line, the model recieves rewards corresponding moved distance
(p find.v.move
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     - prev-goal-loc =posi1
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     color    green
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
   ;!eval! (>= (abs (- =posi1 =posi)) 1)
  ?manual>      
    preparation free
    processor free
    ;execution free
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode 
     ;changed for manipulating dynamics
     next-reward nil
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
     ;!output! (abs (- =posi1 =posi))
   +temporal>
     isa time 
   !eval! (trigger-reward (abs (- =posi1 =posi)))
)

;when the vehicle is off the line and it hasn't moved sice last cycle, the model recieves negative rewards
(p find.v.nega
   =goal>
     isa      move-vehicle
     prev-vehicle-loc =posi1
     - prev-goal-loc =posi1
     vehicle-loc nil
     next-reward t
   =visual-location>
     isa      visual-location
     color    green
     screen-x =posi   
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
   ;!eval! (< (abs (- =posi =posi1)) 1)
  ?manual>      
    preparation free
    processor free
    ;execution free
   ==>
   =goal>
     vehicle-loc =posi
     current-mode =mode
     next-reward nil 
   +visual-location>
     isa      visual-location
     screen-y   highest
     - color    red
     - color    black
     - color    green
     - color    light-gray
     - color    cyan
     ;- color    yellow
     kind text
)


;;IF current goal location is NIL, and there is a yellow/blue object in the VL-buffer, 
;;THEN place the visual location in the goal slot of G-buffer, and place the vehicle position in the VL-buffer

(p find.goal
   =goal>
     isa      move-vehicle
     - vehicle-loc nil
     goal-loc nil
   =visual-location>
     isa      visual-location
     screen-x =posi
     - color red
     - color green
     - color    light-gray
     - color black
   ?visual>
      state    free
   !bind! =mode (return-current-mode)
   !bind! =conf (car (car (no-output (spp (keep.m :u)))))
   !bind! =trust (car (car (no-output (spp (keep.a :u)))))
   ==>
   =goal>
     goal-loc =posi
     current-mode =mode 
     next-reward nil
     self-conf =conf
     trust =trust
)


;;2.3.2 Motor control;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Motor control rules are fired when the vehicle and the goal location are filled
;;;After fire the motor control rules, the vehicle and the goal location are empty

;;2.3.2.1 Manual mode;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;IF there are no needs to change key-state,  
;;THEN nothing


(p keep.m
   =goal>
     isa      move-vehicle
     vehicle-loc =posi1
     goal-loc =posi2
     - goal-loc nil
     - previous-rule press-space-a
   !eval! (or (and (not (equal =posi1 =posi2))
		   (not (equal (return-current-key-state) "STRAIGHT")))
	      (and (equal =posi1 =posi2)
		   (equal (return-current-key-state) "STRAIGHT")))
   !eval! (not (and (equal (return-current-key-state) "LEFT")
		    (<= =posi1 =posi2)))
   !eval! (not (and (equal (return-current-key-state) "RIGHT")
		    (>= =posi1 =posi2)))
   !eval! (equal (return-current-mode) "M")   
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     previous-rule keep-dir
     next-reward t
     prev-vehicle-loc =posi1
     prev-goal-loc =posi2
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )

;;IF current-key-state is "left" and the goal position and the vehicle position is same,  
;;THEN press the j key

(p l.to.s
   =goal>
     isa      move-vehicle
     vehicle-loc =posi1
     ;current-mode  "M"
     goal-loc =posi2
     >= goal-loc =posi1
     - vehicle-loc nil
     - goal-loc nil
     - previous-rule press-space-a
     !eval! (equal (return-current-key-state) "LEFT")
     !eval! (equal (return-current-mode) "M")
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     next-reward t
     previous-rule "STRAIGHT"
     prev-vehicle-loc =posi1
     prev-goal-loc =posi2
   +manual>              
     isa      release-key
     ;isa      press-key
     key       "j"
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )

;;IF current-key-state is "right" and the goal position and the vehicle position is same,  
;;THEN press the l key

(p r.to.s
   =goal>
     isa      move-vehicle
     vehicle-loc =posi1
     ;current-mode  "M"
     goal-loc =posi2
     <= goal-loc =posi1
     - vehicle-loc nil
     - goal-loc nil
     - previous-rule press-space-a
     !eval! (equal (return-current-key-state) "RIGHT")
     !eval! (equal (return-current-mode) "M")    
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     previous-rule "STRAIGHT"
     next-reward t
     prev-vehicle-loc =posi1
     prev-goal-loc =posi2
    +manual>              
    isa      release-key
     ;isa      press-key
     key      "l"
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )

;;IF the goal is at the right of the vehicle, 
;;THEN press j-key


(p to.left
   =goal>
     isa      move-vehicle
     vehicle-loc =posi1
     ;current-mode  "M"
     goal-loc =posi2
     - goal-loc nil
     < goal-loc =posi1
     - previous-rule "LEFT"
     - previous-rule press-space-a
     ;!eval! (null (equal (return-current-key-state) "LEFT"))     
     !eval! (equal (return-current-key-state) "STRAIGHT")
     !eval! (equal (return-current-mode) "M")    
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     previous-rule "LEFT"
     ;next-reward t
     prev-vehicle-loc =posi1
     prev-goal-loc =posi2
    +manual>              
     isa      hold-key
     ;isa      press-key
     key      "j"
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )

;;IF the goal is at the right of the vehicle, 
;;THEN press l-key

(p to.right
   =goal>
     isa      move-vehicle
     vehicle-loc =posi1
     ;current-mode  "M"
     goal-loc =posi2
     - goal-loc nil
     > goal-loc =posi1
     - previous-rule "RIGHT"
     - previous-rule press-space-a
     ;!eval! (null (equal (return-current-key-state) "RIGHT"))
     !eval! (equal (return-current-key-state) "STRAIGHT")
     !eval! (equal (return-current-mode) "M")   
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     previous-rule "RIGHT"
     ;next-reward t
     prev-vehicle-loc =posi1
     prev-goal-loc =posi2
    +manual>              
     isa      hold-key
     ;isa      press-key
     key      "l"
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )



;;IF utility value of keep-m is less than that of keep-a, 
;;THEN press space-key

(p to.auto
   =goal>
     isa      move-vehicle
     ;current-mode  "M"
     - vehicle-loc nil
     - goal-loc nil
     ;previous-rule "STRAIGHT"
     - previous-rule press-space
     - previous-rule press-space-m
     - previous-rule press-space-a
     self-conf =conf
     >= trust =conf
     !eval! (equal (return-current-mode)  "M")    
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     previous-rule press-space-a
   +manual>              
     isa release-all-fingers
     )

(p to.auto2
   =goal>
     isa      move-vehicle
     ;current-mode  "M"
     - vehicle-loc nil
     - goal-loc nil
     ;previous-rule "STRAIGHT"
     - previous-rule press-space
     - previous-rule press-space-m
     - previous-rule press-space-a
     !eval! (equal (return-current-mode)  "M")    
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     previous-rule press-space-a
   +manual>              
     isa release-all-fingers
     )

;;2.3.2.1 Auto Mode;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;IF current mode is auto
;;THEN noting

(p keep.a
   =goal>
    isa  move-vehicle
    ;current-mode  "A"
    vehicle-loc =posi1
    - vehicle-loc nil
    - goal-loc nil
    - previous-rule press-space-a
    !eval! (equal (return-current-mode) "A")    
    ;!eval! (wait-a)    
  ?manual>      
    preparation free
    processor free
    execution free        
  ==>
   =goal>
    vehicle-loc nil
    goal-loc nil
    previous-rule auto
    next-reward t
    prev-vehicle-loc =posi1
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
   )


;;IF utility value of keep-a is less than that of keep-m, 
;;THEN press space-key

(p to.manual
   =goal>
     isa      move-vehicle
     ;current-mode  "M"
     - vehicle-loc nil
     - goal-loc nil
     previous-rule auto
     trust =trust
     >= self-conf =trust
     !eval! (equal (return-current-mode) "A")    
     ;!eval! (>=  (* -1 *thresh*) (- *trust* *self-conf*))
     ;!eval! (>=  (* -1 *thresh*) (- =trust =conf))
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     previous-rule press-space-a
   +manual>              
     isa release-all-fingers
     )

(p to.manual2
   =goal>
     isa      move-vehicle
     ;current-mode  "M"
     - vehicle-loc nil
     - goal-loc nil
     previous-rule auto
     !eval! (equal (return-current-mode) "A")    
 ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     previous-rule press-space-a
   +manual>              
     isa release-all-fingers
     )


(p press.space
   =goal>
     isa      move-vehicle
     previous-rule press-space-a
  ?manual>      
    preparation free
    processor free
    execution free
   ==>
   =goal>
     vehicle-loc nil
     goal-loc nil
     current-mode  nil
     previous-rule press-space
   +manual>              
     isa      punch
     hand     left
     finger   middle
   +visual-location>
     isa      visual-location
     - color    black
     - color    light-gray
     - color    cyan
     - color    blue
     - color    yellow
     kind text
     )

;;2.3.3 Parameter settings for simulation environment;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(setf *actr-enabled-p* t) 
(setf *show-responses* t) 
(goal-focus goal)

;;2.3.3 Initial utility values;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(spp find.v :u 0)
(spp find.goal :u 0)
(spp keep.m :u 5)
(spp to.left :u 0)
(spp l.to.s :u 0)
(spp to.right :u 0)
(spp r.to.s :u 0)
(spp to.auto :u 5)
(spp to.auto2 :u 0)
(spp keep.a :u 5)
(spp to.manual :u 5)
(spp to.manual2 :u 0)
(spp find.v.online2 :u 0 :reward 10)
(spp find.v.ongoal2 :u 0 :reward 10)
(spp find.v.online :u 0)
(spp find.v.ongoal :u 0)
(spp find.v.move :u 0)
(spp find.v.nega :u 0 :reward 0)
)
