(ns gdl.graphics.font
  (:require [clojure.string :as str]
            [x.x :refer [defcomponent]]
            [gdl.lc :as lc]
            [gdl.graphics.batch :refer [batch]]
            [gdl.graphics.unit-scale :refer [*unit-scale*]])
  (:import com.badlogic.gdx.utils.Align
           com.badlogic.gdx.graphics.g2d.BitmapFont))


; 1. check colors if missing/wrong
#_(use 'clojure.pprint)
#_(clojure.pprint/pprint
   (com.badlogic.gdx.graphics.Colors/getColors))
; 2. add new colors & fix in cdq all g/draw-text occurences
; (where more fat font, more border (dmg/hp) and colors, etc...
; (adjust graphics.freetype to add color/border/bordercolor)
; 3. add font to scene2d skin ui

(defn- text-height [^BitmapFont font text]
  (-> text
      (str/split #"\n")
      count
      (* (.getLineHeight font))))

(declare ^BitmapFont default-font)

(defcomponent *ns* _
  (lc/create [_]
    (.bindRoot #'default-font (BitmapFont.))) ; TODO does not work in world scale!
  (lc/dispose [_]
    (.dispose default-font)))

; not sure is a problem (performance) to setScale
; at every draw-text
; could cache it @ font or somewhere for each unit-scale or not even set it back
(defn draw-text [{:keys [font text x y h-align up?]}]
  (let [^BitmapFont font (or font default-font)
        data (.getData font)
        old-scale (.scaleX data)]
    ; background -> get width from glyphlayout only (not necessary yet)
    ;(shape-drawer/filled-rectangle 270 177 250 height color/gray)
    (.setScale data (float (* old-scale *unit-scale*)))
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
    (.setScale data (float old-scale))))

;; **** getting height/width of text with glyphlayout :::
;
; GlyphLayout glyphLayout = new GlyphLayout();
; String item = "Example";
; glyphLayout.setText(font,item);
; float w = glyphLayout.width;
; font.draw(spriteBatch, glyphLayout, (Game.SCREEN_WIDTH - w)/2, y);
;
;; ****
