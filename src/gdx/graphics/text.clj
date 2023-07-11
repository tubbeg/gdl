
; alternative font:
; "anuvverbubbla_8x8.png"
; allowed-characters (range 32 91)
; char-width 8
; all text upper-case only

(def ^:private allowed-characters (set (map char (range 32 126))))
(def ^:private starting-character \space)
(def ^:private char-width-px 6)
(def ^:private char-height-px 8)
(def ^:private horizontal-count 94)

(defn- char-width []
  (* char-width-px *unit-scale*))

(defn- char-height []
  (* char-height-px *unit-scale*))

(declare ^:private font-spritesheet)

(defn- create-font []
  (set-var-root #'font-spritesheet (spritesheet "simple_6x8.png" 6 8)))

; IMPROVEMENT I could memoize the text->spritesheet xpos or even sprites calculation
; so the texts would be memoized immediately and fast
(defn- draw-string
  "Draws the string at position x,y.
  Does not support formatting, centering, shifting, background like
  render-readable-text."
  [x y string scale]
  ;{:pre [(every? allowed-characters string)]}
  ; IMPROVEMENT  too strict, just give a warning and put the not allowed char
  (let [data-array (.getBytes ^String string "US-ASCII")]
    (doseq [i (range (alength data-array))
            :let [char-byte (aget data-array i)
                  index (- char-byte (byte starting-character))
                  x-pos (mod index horizontal-count)
                  char-sprite (get-sprite font-spritesheet [x-pos 0])
                  char-sprite (if (not= scale 1)
                                (get-scaled-copy char-sprite scale)
                                char-sprite)
                  char-width (* scale (char-width))]]
      (draw-image char-sprite
                  (+ x (* char-width i))
                  y))))

;; A 'textseq' here is a sequence of Color or strings (and nils are also allowed, will be ignored)
;; where colors will be set for subsequent strings and
;; after each element a newline will be inserted
;; strings can also contain newlines \n where a newline will be inserted
;; and in metadata can have :scale key

(def ^:private default-font-scale 2)

(defn- scale
  "Text is a textseq or a string."
  [text]
  (or (:scale (meta text))
      default-font-scale))

(defn- line-height
  "Text is a textseq or a string."
  [text]
  (* (char-height) (scale text)))

(defn- textseq->text-lines [textseq]
  (->> textseq
       (remove #(instance? Color %))
       (interpose "\n")
       (apply str)
       split-lines))

(defn- ->textseq
  "Text is a textseq or a string."
  [text]
  (if (string? text) [text] text))

(defn get-text-height
  "Text is a textseq or a string."
  [text]
  (* (line-height text)
     (count (textseq->text-lines (->textseq text)))))

; should work with nil's and Colors in the textseq
(defn get-text-width
  "Text is a textseq or a string."
  [text]
  (* (char-width)
     (apply max (map count (textseq->text-lines (->textseq text))))
     (scale text)))

(defn- render-text* [x y textseq]
  (loop [y (+ y
              (get-text-height textseq)
              (- (line-height textseq)))
         [obj & remaining] textseq]
    (cond
     (instance? Color obj) (do (.setColor *batch* obj)
                               (recur y remaining))

     (string? obj) (if (includes? obj "\n")
                     (recur y
                            (concat (split-lines obj) remaining))
                     (do
                      (draw-string x y obj (:scale (meta textseq)))
                      (recur (- y (line-height textseq))
                             remaining)))))
  (.setColor *batch* white))

; Shift in world coordinate system:
; text will be inside the map tiles (not less than 0)
; problems if world size > screen-width
; then text would not be rendered at right position


; TODO should use viewport-width/height but will delete this text anyway and use bitmapfont
(defn- shift-x [x w]
  (cond (> (+ x w) (.getWidth (graphics))) (- (.getWidth (graphics)) w)
        (< x 0) 0
        :else x))

(defn- shift-y [y h]
  (cond (> (+ y h) (.getHeight (graphics))) (- (.getHeight (graphics)) h)
        (< y 0) 0
        :else y))

(defcolor transparent-black 0 0 0 0.8)

; TODO move scale to opts!
(defn render-readable-text
  "Renders a block of text with bottom left corner at x,y.
  The other lines are rendered below.
  textseq is a sequence of colors or strings. A color will set the color
  for the subsequent strings and each separate string element will be drawn
  below the last. Strings can also contain \n element for that.
  Textseq can also be just one element.
  Do not use :shift in world coordinate system."
  [x y
   {:keys [centerx centery shift background] :as opts
    :or {shift true background true}}
   textseq]
  (let [textseq (if (coll? textseq) textseq [textseq])
        scl (scale textseq) ; gets lost in the next form
        textseq (->> textseq
                     (remove nil?)
                     (map #(if (instance? Color %) % (str %))))
        textseq (with-meta textseq {:scale scl})
        w (get-text-width  textseq)
        h (get-text-height textseq)
        x (if centerx (- x (/ w 2)) x)
        y (if centery (- y (/ h 2)) y)
        x (if shift (shift-x x w) x)
        y (if shift (shift-y y h) y)]
    (when background
      (fill-rect x y w h transparent-black))
    (render-text* x y textseq)))

