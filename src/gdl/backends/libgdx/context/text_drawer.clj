(ns ^:no-doc gdl.backends.libgdx.context.text-drawer
  (:require [clojure.string :as str]
            gdl.context)
  (:import com.badlogic.gdx.graphics.g2d.BitmapFont
           com.badlogic.gdx.utils.Align))

(defn- text-height [^BitmapFont font text]
  (-> text
      (str/split #"\n")
      count
      (* (.getLineHeight font))))

(extend-type gdl.context.Context
  gdl.context/TextDrawer
  (draw-text [{:keys [default-font unit-scale batch]} {:keys [x y text font h-align up? scale]}]
    (let [^BitmapFont font (or font default-font)
          data (.getData font)
          old-scale (float (.scaleX data))]
      (.setScale data (* old-scale (float unit-scale) (float (or scale 1))))
      (.draw font
             batch
             (str text)
             (float x)
             (+ (float y) (float (if up? (text-height font text) 0)))
             (float 0) ; target-width
             (case (or h-align :center)
               :center Align/center
               :left   Align/left
               :right  Align/right)
             false) ; wrap false, no need target-width
      (.setScale data old-scale))))

; TODO pass optionally default-font ?
; TODO is redundant ....
(defn ->context []
  {:default-font (BitmapFont.)}) ; TODO does not draw world-unit-scale idk how possible, maybe setfontdata something
