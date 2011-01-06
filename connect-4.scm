(load-option 'format)

(define board-width 7)
(define board-height 6)
(define connect-n 4)
(define most-positive-fixnum 10000)
(define most-negative-fixnum -10000)

(define (time proc)
  (with-timings proc (lambda (run-time gc-time real-time)
                       (newline)
                       (write (internal-time/ticks->seconds run-time))
                       (write-char #\space)
                       (write (internal-time/ticks->seconds gc-time))
                       (write-char #\space)
                       (write (internal-time/ticks->seconds real-time))
                       (newline))))


(define (memoize function)
  (let ((table (make-equal-hash-table)))
    (lambda (#!rest args)
      (hash-table/lookup table args
                         (lambda (value) value)
                         (lambda ()
                           (let ((result (apply function args)))
                               (hash-table/put! table
                                                args
                                                result)
                               result))))))


;; Returns the position of the given item in the list.
;; Assumes item is a fixnum.
(define (position item list)
  (define (iter list position)
    (if (= item (car list))
        position
        (iter (cdr list) (1+ position))))
  (iter list 0))


(define (enumerate-interval low high)
  (if (> low high)
      '()
      (cons low (enumerate-interval (+ low 1) high))))


(define (empty-board)
  (map
   (lambda (col)
     '())
   (enumerate-interval 1 board-width)))


(define (game-tree board player #!optional last-move)
  (list player
        board
        (delay (moves player board last-move))))


(define (get-moves game-tree)
  (force (caddr game-tree)))


(define (trim-tree game-tree depth)
  (list (car game-tree)
        (cadr game-tree)
        (delay (cond ((zero? depth) '())
                     ;; i.e. game over
                     ((not (list? (get-moves game-tree))) (get-moves game-tree))
                     (else (map (lambda (move)
                             (list (car move) (trim-tree (cadr move) (- depth 1))))
                           (get-moves game-tree)))))))


(define (moves player board last-move)
  (if (and (not (default-object? last-move)) (game-won? board (1+ (remainder player 2)) last-move))
      'game-over
      (filter
       (lambda (move)
         ;;;; I think null? is the idiomatic way to check for an empty list.
         (not (equal? '() move)))
       (map
        (lambda (col)
          (if (column-full? board (- col 1))
              '()
              (list col (game-tree
                         ;; It's error prone constantly mixing 0 and 1 indexed columns.
                         (place-counter board (- col 1) player)
                         (1+ (remainder player 2))
                         col))))
        (inside-first (enumerate-interval 1 board-width))))))

;;(display-game-tree (trim-tree (game-tree (empty-board) 1) 2))


(define (display-game-tree game-tree)
  (define (display-with-indent obj depth)
    (let ((indent (* depth 2)))
      (format #t "~A~A~%" (make-string indent #\space) obj)))
  (define (display-branch branch depth)
    (display-with-indent (car branch) depth)
    (display-with-indent (cadr branch) depth)
    (if (equal? 'game-over (get-moves branch))
        (display-with-indent 'game-over depth)
        (for-each (lambda (move)
                    (display-with-indent (car move) depth)
                    (display-branch (cadr move) (1+ depth)))
                  (get-moves branch))))
  (newline)
  (display-branch game-tree 1))


;; This is minimax with alpha-beta pruning.
;; This was taken prety much as-is from Land of Lisp. (Which is great BTW.)
(define (ab-rate-position game-tree player upper-limit lower-limit)
  (let ((moves (get-moves game-tree)))
    (if (and (list? moves) (not (null? moves)))
        (if (= player (car game-tree))
            (apply max (ab-get-ratings-max game-tree
                                           player
                                           upper-limit
                                           lower-limit))
            (apply min (ab-get-ratings-min game-tree
                                           player
                                           upper-limit
                                           lower-limit)))
        (score-position game-tree player))))


;; Scores a leaf node.
;; Points are only given for wins, there's no attempt to rate boards
;; from games which are in-progress.
(define (score-position game-tree player)
  (let ((moves (get-moves game-tree)))
    (cond ((null? moves) 0) ;; no more moves - draw of end of trimmed tree
          ;; Assume game-over as we're only called when this is
          ;; is a leaf-node, therefore must be either no more
          ;; moves or game over.
          ((equal? (car game-tree) player) -1) ;; lost
          (else 1))))


(define (ab-get-ratings-max game-tree player upper-limit lower-limit)
  (define (f moves lower-limit)
    (if (null? moves)
        '()
        (let ((x (ab-rate-position (cadr (car moves))
                                   player
                                   upper-limit
                                   lower-limit)))
          (if (>= x upper-limit)
              (list x)
              (cons x (f (cdr moves) (max x lower-limit)))))))
  (f (get-moves game-tree) lower-limit))

(define (ab-get-ratings-min game-tree player upper-limit lower-limit)
  (define (f moves upper-limit)
    (if (null? moves)
        '()
        (let ((x (ab-rate-position (cadr (car moves))
                                   player
                                   upper-limit
                                   lower-limit)))
          (if (<= x lower-limit)
              (list x)
              (cons x (f (cdr moves) upper-limit))))))
  (f (get-moves game-tree) upper-limit))


(define (ab-pick-move game-tree)
  (let ((ratings (ab-get-ratings-max game-tree
                                     (car game-tree)
                                     most-positive-fixnum
                                     most-negative-fixnum)))
    (car (list-ref (get-moves game-tree) (position (apply max ratings) ratings)))))


;; Turns a board (which is stored as a list of columns) in to a list of rows.
(define (transpose board)
  (define (iter rest-of-rows)
    (if (every null? rest-of-rows)
        '()
        (cons
         (map
          (lambda (col)
            (if (null? col)
                0
                (car col)))
          rest-of-rows)
         (iter (map
                (lambda (col)
                  (if (null? col)
                      '()
                      (cdr col)))
                rest-of-rows)))))
  (iter board))


;; Checks the whole board for winning rows.
;; No longer used.
(define (game-over? board player)
  (or (horizontal-row? board player)
      (vertical-row? board player)
      (left-diagonal-row? board player)
      (right-diagonal-row? board player)))

(define (horizontal-row? board player)
  (vertical-row? (transpose board) player))

(define (vertical-row? board player)
  (any (lambda (row)
         (winning-row? row player))
       board))

;; Adds padding to each column such that lines which were previously
;; on the \ diagonal will now be on the horizontal.
(define (transpose-tilt-left board)
  (define (iter rest-of-board)
    (if (null? rest-of-board)
        '()
        (cons (car rest-of-board)
              (iter (map
                     (lambda (col)
                       (cons 0 col))
                     (cdr rest-of-board))))))
  (iter board))

(define (transpose-tilt-right board)
  (reverse (transpose-tilt-left (reverse board))))

(define (left-diagonal-row? board player)
  (vertical-row? (transpose (transpose-tilt-left board)) player))

(define (right-diagonal-row? board player)
  (vertical-row? (transpose (transpose-tilt-right board)) player))


;; Tests for the end of the game, only
;; checking for lines which might have
;; been completed in the last move.
(define (game-won? board player last-move)
  (let ((x (- last-move 1))
        (y (- (length (list-ref board (- last-move 1))) 1)))
    (or (winning-row? (list-ref board x) player)
        (winning-row? (line-through board x y 1) player)
        (winning-row? (line-through board x y 0) player)
        (winning-row? (line-through board x y -1) player))))


;; Origin bottom-left, zero indexed.
;; Iterates over the board from left to right
;; collecting a single counter from each column.
;; If delta-y is 0 the horizontal row through
;; y is collected. When delta-y is -1 the main
;; diagonal through x,y is collected and when
;; delta-y is +1 the minor diagonal though x,y
;; is collected.
;; Probably better written using map.
(define (line-through board x y delta-y)
  (define (iter rest-of-board cy diag)
    (cond ((null? rest-of-board) diag)
          ((and (< cy (length (car rest-of-board))) (>= cy 0))
           (iter (cdr rest-of-board) (+ cy delta-y) (cons (list-ref (car rest-of-board) cy) diag)))
          (else (iter (cdr rest-of-board) (+ cy delta-y) (cons 0 diag)))))
  (iter board (- y (* x delta-y)) '()))


(define (winning-row? row player)
  (>= (longest-line row player) connect-n))


(define (longest-line row player)
  (define (iter rest-of-row current-length max-length)
    (cond ((null? rest-of-row) max-length)
          ((= (car rest-of-row) player)
           (iter (cdr rest-of-row) (1+ current-length) (max max-length (1+ current-length))))
          (else (iter (cdr rest-of-row) 0 max-length))))
  (iter row 0 0))


(define (column-full? board col)
  (= (length (list-ref board col)) board-height))


(define (place-counter board col player)
  (define (iter k rest-of-cols)
    (if (zero? k)
        (cons
         (append
          (car rest-of-cols)
          (list player))
         (cdr rest-of-cols))
        (cons
         (car rest-of-cols)
         (iter (- k 1) (cdr rest-of-cols)))))
  (iter col board))


;; Used to order the moves in the game tree in such a way that should
;; help alpha beta pruning's efficienct. Also has the nice side-effect
;; of having the cpu place counters in the center of the board when
;; all moves are scored equally, rather than always placing its
;; counter in column 0.
;; '(1 2 3 4 5 6) becomes '(4 3 5 2 6 1)
(define (inside-first list)
  (define (zip list1 list2)
    (cond ((and (null? list1) (null? list2)) '())
          ((null? list2) (cons (car list1) '()))
          ((cons (car list1) (cons (car list2) (zip (cdr list1) (cdr list2)))))))
  (let ((mid (quotient (length list) 2)))
    (zip (list-tail list mid) (reverse (list-head list mid)))))


(define (red)
  (display (string-append (string #\escape) "[31m")))

(define (yellow)
  (display (string-append (string #\escape) "[33m")))

(define (default-color)
  (display (string-append (string #\escape) "[0m")))

(define (display-counter player)
  (cond ((= player 1) (red))
        ((= player 2) (yellow))
        (else default-color))
  (display "◉")
  (default-color))


(define (game-loop p1 p2 game-tree)
  (if (or (equal? 'game-over (get-moves game-tree))
          (null? (get-moves game-tree)))
      (display 'game-over)
      (begin
        (newline)
        (display-board (cadr game-tree))
        (game-loop p1 p2 (cadr (assoc ((if (= (car game-tree) 1) p1 p2) game-tree) (get-moves game-tree)))))))


(define (display-board-simple board)
  (for-each (lambda (row)
              (newline)
              (display row))
            (reverse (transpose board))))


(define (display-board board)
  (for-each (lambda (row)
              (for-each (lambda (counter)
                          (display-counter counter))
                        row)
              (newline))
            (reverse (transpose board))))


(define (make-human-player name)
  (lambda (game-tree)
    (display name)
    (display " to move")
    (newline)
    (string->number (read-line))))


(define (make-ab-player depth name)
  (lambda (game-tree)
    (display name)
    (display " is thinking")
    (newline)
    (time (lambda () (ab-pick-move (trim-tree game-tree depth))))))

;; I start seeing out of memory errors at a depth of 8 or 9.
(define cpu (make-ab-player 8 "CPU"))
(define human (make-human-player "Human"))

(define random-player
  (lambda (tree)
    (1+ (random board-width))))

(define (new-game p1 p2)
  (game-loop p1 p2 (game-tree (empty-board) 1)))


;;(new-game human human)
