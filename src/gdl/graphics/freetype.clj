(ns gdl.graphics.freetype
  (:require [gdl.app :as app]
            [gdl.files :as files])
  (:import [com.badlogic.gdx.graphics Texture$TextureFilter]
           [com.badlogic.gdx.graphics.g2d BitmapFont]
           [com.badlogic.gdx.graphics.g2d.freetype
            FreeTypeFontGenerator
            FreeTypeFontGenerator$FreeTypeFontParameter]))

(def ^:private quality-scaling 2)

(defn- ->params [size]
  (let [params (FreeTypeFontGenerator$FreeTypeFontParameter.)]
    (set! (.size params) (* size quality-scaling))
    ; .color and this:
    ;(set! (.borderWidth parameter) 1)
    ;(set! (.borderColor parameter) red)
    (set! (.minFilter params) Texture$TextureFilter/Linear) ; because scaling to world-units
    (set! (.magFilter params) Texture$TextureFilter/Linear)
    params))

(defn generate [ttf-file size]
  (let [generator (-> ttf-file files/internal FreeTypeFontGenerator.)
        font (.generateFont generator (->params size))]
    (.dispose generator)
    (.setScale (.getData font) (float (/ quality-scaling)))
    (set! (.markupEnabled (.getData font)) true)
    (.setUseIntegerPositions font false) ; otherwise scaling to world-units (/ 1 48)px not visible
    font))

; there is a asset loader, then we wouldn't need to dispose here
; but its also a way of managing it no
(defmacro def-font [symbol & params] ; similar to graphics/default-font declaration
  `(app/defmanaged ~(vary-meta symbol merge {:dispose true :tag BitmapFont})
     (generate ~@params)))


; TODO graphics/def-font
; and here just (freetype/generate)
; anyone can def-font any bitmap fonts ?

; def font just type hints as bitmapfont
; defbitmapfont ?
; and disposes
; thats actually not much ?
; and initializes
