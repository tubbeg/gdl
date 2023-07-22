; TODO WARNING: colors are mutable, even the static ones in com.badlogic.gdx.graphics.Color
(ns gdx.graphics.color
  (:require [clojure.string :as str])
  (:import com.badlogic.gdx.graphics.Color))

; Idea:
; * import all of com.badlogic.gdx.graphics.Color
; and use .cpy to make immutable colors
; -> but still mutable color underneath !

; https://github.com/ngrunwald/gavagai

; TODO how to keep colors in the docs separate
; some prefix to the name color/white == statics ??
; color/*white ?

; TODO type hints not working /  add type hints to all fns ?
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
   `(def ~(with-meta color {:tag Color}) ~(symbol (str "Color/" (str/upper-case color))))))
; TODO import everything from 'Color' ???

(defn rgb
  ([r g b]
   (rgb r g b 1))
  ([r g b a]
   (Color. (float r) (float g) (float b) (float a))))

; TODO can make automatic type hint here also !
; and add to named colors for text thingy
(defmacro defrgb [symbol & rgb-args]
  `(def ~symbol (rgb ~@rgb-args)))

(defn multiply-color [^Color color ^Color other]
  (.mul (.cpy color) other))

(defn- mul-without-alpha [^Color color value]
  (let [new-color (.mul (.cpy color) (float value))]
    (set! (.a new-color) (.a color))
    new-color))

(defn darker   [color scale] (mul-without-alpha color (- 1 scale)))
(defn brighter [color scale] (mul-without-alpha color (+ 1 scale)))
