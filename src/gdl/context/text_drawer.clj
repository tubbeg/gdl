(ns gdl.context.text-drawer
  (:require [clojure.string :as str])
  (:import com.badlogic.gdx.graphics.g2d.BitmapFont
           com.badlogic.gdx.utils.Align))

(defn- text-height [^BitmapFont font text]
  (-> text
      (str/split #"\n")
      count
      (* (.getLineHeight font))))

(defn- extend-context-class [klass]
  (extend-type klass
    gdl.protocols/TextDrawer
    (draw-text [{:keys [default-font unit-scale batch]} {:keys [font text x y h-align up?]}]
      (let [^BitmapFont font (or font default-font)
            data (.getData font)
            old-scale (.scaleX data)]
        (.setScale data (float (* old-scale unit-scale)))
        (.draw font
               batch
               (str text)
               (float x)
               (float (+ y (if up? (text-height font text) 0)))
               (float 0) ; target-width
               (case (or h-align :center)
                 :center Align/center
                 :left   Align/left
                 :right  Align/right)
               false) ; wrap false, no need target-width
        (.setScale data (float old-scale))))))

; TODO pass optionally default-font ?
(defn extend-and-create-context [klass]
  (extend-context-class klass)
  {:default-font (BitmapFont.)}) ; TODO does not draw world-unit-scale idk how possible, maybe setfontdata something
