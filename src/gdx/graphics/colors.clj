(doseq [color '[white
                yellow
                red
                blue
                green
                black
                gray
                cyan
                pink
                orange
                magenta]]
  (eval
   `(def ^color ~color ~(symbol (str "Color/" (upper-case color))))))

(defn color
  ([r g b]
   (color r g b 1))
  ([r g b a]
   (Color. (float r) (float g) (float b) (float a))))

(defmacro defcolor [namesym & args]
  `(def ~namesym (color ~@args)))

(defn multiply-color [^Color color ^Color other]
  (.mul (.cpy color) other))

(defn- mul-without-alpha [^Color color value]
  (let [new-color (.mul (.cpy color) (float value))]
    (set! (.a new-color) (.a color))
    new-color))

(defn darker   [color scale] (mul-without-alpha color (- 1 scale)))
(defn brighter [color scale] (mul-without-alpha color (+ 1 scale)))
