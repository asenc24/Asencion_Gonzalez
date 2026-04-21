#lang racket

;; Programa: lee `data.io` con líneas del tipo
;; (V=[a,b,...],A=[(u,v),(x,y),...]) y detecta propiedades de grafos.

(require racket/string racket/set racket/hash racket/match)

(define (trim s) (string-trim s))

; Parseo: extrae vértices y aristas
(define (parse-line line)
  (let* ((s (string-trim line))
         (v-pos (string-contains? s "V="))
         (v-content (and v-pos
                         (let ((open (string-index s #\[ v-pos)))
                           (and open
                                (let ((close (string-index s #\] open)))
                                  (and close (substring s (+ open 1) close)))))))
         (a-pos (string-contains? s "A="))
         (a-content (and a-pos
                         (let ((open (string-index s #\[ a-pos)))
                           (and open
                                (let ((close (string-index s #\] open)))
                                  (and close (substring s (+ open 1) close))))))))
    (define vertices
      (if (or (not v-content) (string-blank? v-content))
          '()
          (map (lambda (t) (string->symbol (string-trim t)))
               (filter (lambda (x) (not (string-blank? x)))
                       (map string-trim (string-split v-content ","))))))
    (define edges-list
      (let loop ((s2 (or a-content "")) (out '()))
        (let ((pos (string-index s2 #\())))
          (if (or (not pos) (string-blank? s2))
              (reverse out)
              (let* ((rest (substring s2 (+ pos 1)))
                     (close-pos (string-index rest #\))))
                (if (not close-pos)
                    (reverse out)
                    (let* ((inside (substring rest 0 close-pos))
                           (parts (map string-trim (string-split inside ",")))
                           (u (string->symbol (first parts)))
                           (v (string->symbol (second parts))))
                      (loop (substring rest (+ close-pos 1)) (cons (list u v) out))))))))
    (values (list->set vertices) edges-list))

; Normaliza aristas: elimina lazos, ordena pares y quita duplicados
(define (normalize-edges edges)
  (remove-duplicates
   (filter identity
    (map (lambda (e)
           (match e
             [(list u v)
              (if (equal? u v)
                  #f
                  (let ([su (symbol->string u)] [sv (symbol->string v)])
                    (if (string<? su sv) (list u v) (list v u))))]
             [_ #f]))
         edges))
   equal?))

; Construye grafo: vértices (set), aristas (lista de pares), adyacencia (hash)
(define (build-graph V edges)
  (define E (normalize-edges edges))
  (define V-all (foldl (lambda (e acc) (set-add (set-add acc (first e)) (second e))) V E))
  (define adj (make-hash))
  (for ([v (in-list (set->list V-all))]) (hash-set! adj v '()))
  (for ([e (in-list E)])
    (let ([u (first e)] [v (second e)])
      (unless (member v (hash-ref adj u '())) (hash-set! adj u (cons v (hash-ref adj u '()))))
      (unless (member u (hash-ref adj v '())) (hash-set! adj v (cons u (hash-ref adj v '()))))))
  (values V-all E adj))

; Auxiliares
(define (degree v adj) (length (hash-ref adj v '())))

; Conectividad
(define (connected? V adj)
  (if (zero? (set-count V)) #t
      (let ([start (first (set->list V))])
        (let loop ((q (list start)) (seen (set start)))
          (if (null? q)
              (= (set-count seen) (set-count V))
              (let* ([u (first q)] [restq (rest q)] [nbrs (hash-ref adj u '())]
                     [new (filter (lambda (x) (not (set-member? seen x))) nbrs)])
                (loop (append restq new) (set-union seen (list->set new))))))))

; Bipartito
(define (bipartite? V adj)
  (define colors (make-hash))
  (define (bfs start)
    (unless (hash-has-key? colors start)
      (hash-set! colors start 1)
      (let loop ((q (list start)))
        (if (null? q) #t
            (let ([u (first q)] [nbrs (hash-ref adj u '())])
              (for ([v (in-list nbrs)])
                (let ([cv (hash-ref colors v #f)])
                  (cond [(not cv) (hash-set! colors v (- (hash-ref colors u)))]
                        [(= cv (hash-ref colors u)) (raise (exn:fail "conflict"))]
                        [else #f])))
              (loop (remove-duplicates (append (rest q) nbrs)))))))
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (for ([v (in-list (set->list V))]) (bfs v))
    #t))

; Completitud
(define (complete? V E)
  (let ([n (set-count V)]) (= (length E) (quotient (* n (- n 1)) 2))))

; Bipartito completo
(define (complete-bipartite? V adj)
  (if (not (bipartite? V adj)) #f
      (let ([colors (make-hash)])
        (for ([v (in-list (set->list V))])
          (when (not (hash-has-key? colors v))
            (hash-set! colors v 1)
            (let loop ((q (list v)))
              (when (not (null? q))
                (let ([u (first q)])
                  (for ([w (in-list (hash-ref adj u '()))])
                    (unless (hash-has-key? colors w)
                      (hash-set! colors w (- (hash-ref colors u)))
                      (set! q (append q (list w)))))
                  (loop (rest q)))))))
        (define part1 (filter (lambda (x) (= (hash-ref colors x) 1)) (set->list V)))
        (define part2 (filter (lambda (x) (= (hash-ref colors x) -1)) (set->list V)))
        (= (length (for/list ([u (in-list part1)] [v (in-list part2)]) (if (member v (hash-ref adj u '())) 1 0)))
           (* (length part1) (length part2))))))

; Árbol
(define (tree? V E adj) (and (connected? V adj) (= (length E) (- (set-count V) 1))))

; Euleriano (0 o 2 vértices de grado impar y conectado)
(define (eulerian? V adj)
  (let ([odds (for/fold ([acc 0]) ([v (in-list (set->list V))]) (if (odd? (degree v adj)) (+ acc 1) acc))])
    (and (connected? V adj) (or (= odds 0) (= odds 2)))))

; Combinaciones para conjuntos pequeños
(define (combinations lst k)
  (cond [(= k 0) (list '())]
        [(null? lst) '()]
        [else (let ([x (first lst)] [xs (rest lst)])
                (append (map (lambda (c) (cons x c)) (combinations xs (- k 1))) (combinations xs k)))]))

; Auxiliar: existe arista (u,v) en E-set (indiferente del orden)
(define (edge-exists? E-set u v)
  (or (member (list u v) E-set) (member (list v u) E-set)))

; Detección K5 y K3,3 (búsqueda por subconjuntos)
(define (k5-subgraph? V E-set)
  (for/or ([c (in-list (combinations (set->list V) 5))])
    (for/and ([i (in-range 0 5)] [j (in-range (+ i 1) 5)])
      (let ([u (list-ref c i)] [v (list-ref c j)])
        (edge-exists? E-set u v)))))

; Para K3,3: probar particiones en cada 6-subconjunto
(define (k3-3-subgraph? V E-set)
  (define (all-pairs? left right)
    (for/and ([u (in-list left)] [v (in-list right)]) (edge-exists? E-set u v)))
  (for/or ([c (in-list (combinations (set->list V) 6))])
    (for/or ([left (in-list (combinations c 3))])
      (let ([right (filter (lambda (x) (not (member x left))) c)])
        (and (= (length right) 3) (all-pairs? left right))))))

; Planar heurístico
(define (planar-heuristic? V E)
  (let ([n (set-count V)] [m (length E)])
    (and (if (<= n 2) #t (<= m (- (* 3 n) 6))) (not (or (k5-subgraph? V E) (k3-3-subgraph? V E))))))

(define (check-all-properties-from-graph V E adj)
  (let ([n (set-count V)] [m (length E)])
    (filter identity
      (list (if (zero? n) "Grafo Nulo" #f)
            (if (zero? m) "Grafo Vacio" #f)
            (if (= n 1) "Grafo Unitario" #f)
            (if (connected? V adj) "Grafo Conexo" #f)
            (if (complete? V E) "Grafo Completo" #f)
            (if (bipartite? V adj) "Grafo Bipartido" #f)
            (if (complete-bipartite? V adj) "Grafo Bipartito Completo" #f)
            (if (tree? V E adj) "Arbol" #f)
            (if (eulerian? V adj) "Grafo Euleriano" #f)
            (if (planar-heuristic? V E) "Grafo Plano (heur)" #f)))))

; MAIN
(define (main)
  (define infile "data.io")
  (if (not (file-exists? infile)) (printf "Archivo data.io no encontrado.~n")
      (call-with-input-file infile
        (lambda (in)
          (let loop ((i 1))
            (let ((line (read-line in 'any)))
              (if (eof-object? line) (void)
                  (begin
                    (let ((s (string-trim line)))
                      (when (and (not (string-empty? s)) (not (char=? #\; (string-ref s 0))))
                        (with-handlers ([exn:fail? (lambda (e) (printf "Linea ~a: error parseando — ~a~n" i (exn-message e)))])
                          (define-values (V edges) (parse-line s))
                          (define-values (V-all E adj) (build-graph V edges))
                          (define props (check-all-properties-from-graph V-all E adj))
                          (printf "Caso ~a: tipos -> ~a~n" i (if (null? props) '(ninguno) props)))))
                    (loop (+ i 1)))))))))

(main)
#lang racket

;; Programa: lee `data.io` con líneas del tipo
;; (V=[a,b,...],A=[(u,v),(x,y),...]) y detecta propiedades de grafos.

(require racket/string racket/set racket/hash racket/match)

(define (trim s) (string-trim s))

; Parseo: extrae vértices y aristas
 (define (parse-line line)
   (let* ((s (string-trim line))
          (v-content (let ((pos (string-contains? s "V=")))
                       (and pos (let ((open (string-index s #\[ pos)))
                                  (and open (let ((close (string-index s #\] open)))
                                             (and close (substring s (+ open 1) close))))))))
          (a-content (let ((pos (string-contains? s "A=")))
                       (and pos (let ((open (string-index s #\[ pos)))
                                  (and open (let ((close (string-index s #\] open)))
                                             (and close (substring s (+ open 1) close)))))))))
     (define vertices
       (if (or (not v-content) (string-blank? v-content))
           '()
           (map (λ (t) (string->symbol (string-trim t)))
                (filter (λ (x) (not (string-blank? x)))
                        (map string-trim (string-split v-content ","))))))
     (define edges-list
       (let loop ((s2 (or a-content "")) (out '()))
         (let ((pos (string-index s2 #\())))
           (if (or (not pos) (string-blank? s2))
               (reverse out)
               (let* ((rest (substring s2 (+ pos 1)))
                      (close-pos (string-index rest #\))))
                 (if (not close-pos)
                     (reverse out)
                     (let* ((inside (substring rest 0 close-pos))
                            (parts (map string-trim (string-split inside ",")))
                            (u (string->symbol (first parts)))
                            (v (string->symbol (second parts))))
                       (loop (substring rest (+ close-pos 1)) (cons (list u v) out))))))))
     (values (list->set vertices) edges-list))

; Normaliza aristas: elimina lazos, ordena pares y quita duplicados
(define (normalize-edges edges)
  (remove-duplicates
   (filter identity
    (map (λ (e)
           (match e
             [(list u v)
              (if (equal? u v)
                  #f
                  (let ([su (symbol->string u)] [sv (symbol->string v)])
                    (if (string<? su sv) (list u v) (list v u))))]
             [_ #f]))
         edges))
   equal?))

; Construye grafo: vértices (set), aristas (lista de pares), adyacencia (hash)
(define (build-graph V edges)
  (define E (normalize-edges edges))
  (define V-all (foldl (λ (e acc) (set-add (set-add acc (first e)) (second e))) V E))
  (define adj (make-hash))
  (for ([v (in-list (set->list V-all))]) (hash-set! adj v '()))
  (for ([e (in-list E)])
    (let ([u (first e)] [v (second e)])
      (unless (member v (hash-ref adj u '())) (hash-set! adj u (cons v (hash-ref adj u '()))))
      (unless (member u (hash-ref adj v '())) (hash-set! adj v (cons u (hash-ref adj v '()))))))
  (values V-all E adj))

; Auxiliares
(define (degree v adj) (length (hash-ref adj v '())))

; Conectividad
(define (connected? V adj)
  (if (zero? (set-count V)) #t
      (let ([start (first (set->list V))])
        (let loop ([q (list start)] [seen (set start)])
          (if (null? q)
              (= (set-count seen) (set-count V))
              (let* ([u (first q)] [restq (rest q)] [nbrs (hash-ref adj u '())]
                     [new (filter (λ (x) (not (set-member? seen x))) nbrs)])
                (loop (append restq new) (set-union seen (list->set new))))))))

; Bipartito
(define (bipartite? V adj)
  (define colors (make-hash))
  (define (bfs start)
    (unless (hash-has-key? colors start)
      (hash-set! colors start 1)
      (let loop ((q (list start)))
        (if (null? q) #t
            (let ([u (first q)] [nbrs (hash-ref adj u '())])
              (for ([v (in-list nbrs)])
                (let ([cv (hash-ref colors v #f)])
                  (cond [(not cv) (hash-set! colors v (- (hash-ref colors u)))]
                        [(= cv (hash-ref colors u)) (raise (exn:fail "conflict"))]
                        [else #f])))
              (loop (remove-duplicates (append (rest q) nbrs)))))))
  (with-handlers ([exn:fail? (λ (_) #f)])
    (for ([v (in-list (set->list V))]) (bfs v))
    #t))

; Completitud
(define (complete? V E)
  (let ([n (set-count V)]) (= (length E) (quotient (* n (- n 1)) 2))))

; Bipartito completo
(define (complete-bipartite? V adj)
  (if (not (bipartite? V adj)) #f
      (let ([colors (make-hash)])
        (for ([v (in-list (set->list V))])
          (when (not (hash-has-key? colors v))
            (hash-set! colors v 1)
            (let loop ((q (list v)))
              (when (not (null? q))
                (let ([u (first q)])
                  (for ([w (in-list (hash-ref adj u '()))])
                    (unless (hash-has-key? colors w)
                      (hash-set! colors w (- (hash-ref colors u)))
                      (set! q (append q (list w)))))
                  (loop (rest q)))))))
        (define part1 (filter (λ (x) (= (hash-ref colors x) 1)) (set->list V)))
        (define part2 (filter (λ (x) (= (hash-ref colors x) -1)) (set->list V)))
        (= (length (for/list ([u (in-list part1)] [v (in-list part2)]) (if (member v (hash-ref adj u '())) 1 0)))
           (* (length part1) (length part2))))))

; Árbol
(define (tree? V E adj) (and (connected? V adj) (= (length E) (- (set-count V) 1))))

; Euleriano (0 o 2 vértices de grado impar y conectado)
(define (eulerian? V adj)
  (let ([odds (for/fold ([acc 0]) ([v (in-list (set->list V))]) (if (odd? (degree v adj)) (+ acc 1) acc))])
    (and (connected? V adj) (or (= odds 0) (= odds 2)))))

; Combinaciones para conjuntos pequeños
(define (combinations lst k)
  (cond [(= k 0) (list '())]
        [(null? lst) '()]
        [else (let ([x (first lst)] [xs (rest lst)])
                (append (map (λ (c) (cons x c)) (combinations xs (- k 1))) (combinations xs k)))]))

; Detección K5 y K3,3 (búsqueda por subconjuntos)
; Auxiliar: existe arista (u,v) en E-set (indiferente del orden)
(define (edge-exists? E-set u v)
  (or (member (list u v) E-set) (member (list v u) E-set)))

; Detección K5 y K3,3 (búsqueda por subconjuntos)
(define (k5-subgraph? V E-set)
  (for/or ([c (in-list (combinations (set->list V) 5))])
    (for/and ([i (in-range 0 5)] [j (in-range (+ i 1) 5)])
      (let ([u (list-ref c i)] [v (list-ref c j)])
        (edge-exists? E-set u v)))))

; Para K3,3: probar particiones en cada 6-subconjunto
(define (k3-3-subgraph? V E-set)
  (define (all-pairs? left right)
    (for/and ([u (in-list left)] [v (in-list right)]) (edge-exists? E-set u v)))
  (for/or ([c (in-list (combinations (set->list V) 6))])
    (for/or ([left (in-list (combinations c 3))])
      (let ([right (filter (λ (x) (not (member x left))) c)])
        (and (= (length right) 3) (all-pairs? left right))))))

; Planar heurístico
(define (planar-heuristic? V E)
  (let ([n (set-count V)] [m (length E)])
    (and (if (<= n 2) #t (<= m (- (* 3 n) 6))) (not (or (k5-subgraph? V E) (k3-3-subgraph? V E)) ))))

(define (check-all-properties-from-graph V E adj)
  (let ([n (set-count V)] [m (length E)])
    (filter identity
      (list (if (zero? n) "Grafo Nulo" #f)
            (if (zero? m) "Grafo Vacio" #f)
            (if (= n 1) "Grafo Unitario" #f)
            (if (connected? V adj) "Grafo Conexo" #f)
            (if (complete? V E) "Grafo Completo" #f)
            (if (bipartite? V adj) "Grafo Bipartido" #f)
            (if (complete-bipartite? V adj) "Grafo Bipartito Completo" #f)
            (if (tree? V E adj) "Arbol" #f)
            (if (eulerian? V adj) "Grafo Euleriano" #f)
            (if (planar-heuristic? V E) "Grafo Plano (heur)" #f)))))

; MAIN
(define (main)
  (define infile "data.io")
  (if (not (file-exists? infile)) (printf "Archivo data.io no encontrado.\n")
      (call-with-input-file infile
        (lambda (in)
          (let loop ((i 1))
            (let ((line (read-line in 'any)))
              (if (eof-object? line) (void)
                  (begin
                    (let ((s (string-trim line)))
                      (when (and (not (string-empty? s)) (not (char=? #\; (string-ref s 0))))
                        (with-handlers ([exn:fail? (λ (e) (printf "Linea ~a: error parseando — ~a\n" i (exn-message e)))])
                          (define-values (V edges) (parse-line s))
                          (define-values (V-all E adj) (build-graph V edges))
                          (define props (check-all-properties-from-graph V-all E adj))
                          (printf "Caso ~a: tipos -> ~a~n" i (if (null? props) '(ninguno) props)))))
                    (loop (+ i 1)))))))))

))))

(main)