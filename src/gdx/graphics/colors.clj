; IMPROVEMENT: could tag ^Color
(defmacro ^:private defcolors [& names]
  `(do
     ~@(map #(list 'def % (symbol (str "Color/" (upper-case %)))) names)))

(defcolors white yellow red blue green black gray cyan pink orange magenta)

(defn rgbcolor
  ([r g b]
   (rgbcolor r g b 1))
  ([r g b a]
   (Color. (float r) (float g) (float b) (float a))))

(defmacro defcolor [namesym & args]
  `(def ~namesym (rgbcolor ~@args)))

(defn- mul [^Color color value]
  (let [color (.mul (.cpy color) (float value))]
    (set! (.a color) 1) ; ??? TODO
    color))

(defn multiply-color [^Color color ^Color other]
  (.mul (.cpy color) other))

(defn darker   [color scale] (mul color (- 1 scale)))
(defn brighter [color scale] (mul color (+ 1 scale)))

