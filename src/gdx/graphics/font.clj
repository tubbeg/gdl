(ns gdx.graphics.font
  (:require [gdx.utils :refer (set-var-root)]
            [gdx.app :as app]
            [gdx.files :as files]
            [gdx.graphics :as g])
  (:import [com.badlogic.gdx.graphics Texture$TextureFilter]
           [com.badlogic.gdx.graphics.g2d BitmapFont]
           [com.badlogic.gdx.graphics.g2d.freetype
            FreeTypeFontGenerator
            FreeTypeFontGenerator$FreeTypeFontParameter]))

; was not working
;(.add ui/skin "default-font" font BitmapFont)

(def ^:private quality-scaling 2)

(defn- ->params [size]
  (let [params (FreeTypeFontGenerator$FreeTypeFontParameter.)]
    (set! (.size params) (* size quality-scaling))
    ; TODO .color also
    ; and this:
    ;(set! (.borderWidth parameter) 1)
    ;(set! (.borderColor parameter) red)
    (set! (.minFilter params) Texture$TextureFilter/Linear) ; because scaling to world-units
    (set! (.magFilter params) Texture$TextureFilter/Linear)
    params))

(defn generate [ttf-file size]
  (let [generator (-> ttf-file files/get FreeTypeFontGenerator.)
        font (.generateFont generator (->params size))]
    (.dispose generator)
    (.setScale (.getData font) (float (/ quality-scaling)))
    (set! (.markupEnabled (.getData font)) true)
    (.setUseIntegerPositions font false) ; otherwise scaling to world-units (/ 1 48)px not visible
    font))

; there is a asset loader, then we wouldn't need to dispose here
; but its also a way of managing it no
(defmacro def-font [symbol & params]
  `(app/defmanaged ~(with-meta symbol {:dispose true :tag BitmapFont})
     (font/generate ~@params)))

; not sure is a problem (performance) to setScale
; at every draw-text
; could cache it @ font or somewhere for each unit-scale or not even set it back
(defn draw-text [font text x y]
  (let [old-scale (.scaleX (.getData font))]
    (.setScale (.getData font) (float (* old-scale g/*unit-scale*)))
    (.draw font g/batch ^String (str text) (float x) (float y))
    (.setScale (.getData font) (float old-scale))))


(import 'com.badlogic.gdx.utils.Align)

; NOTE:
; * font at x,y
; x/y is top left point of fontbounds

; or graphics.text :as text?
; text/draw [font text x y h-align] ?
; text/def-font  ?

; or font/draw-text


; TODO align is only horizontal alignment !
(defn draw-text-align [font text x y align]
  (.setScale (.getData font) (float g/*unit-scale*))
  (.draw font g/batch ^String (str text) (float x) (float y)
         (float 0) ; target-width
         align; align
         false ; wrap false, no need target-width
         ))

; TODO height is simple just font size ... ( & scale berucksichtigen)

;draw(Batch batch,
;           java.lang.CharSequence str,
;           float x,
;           float y,
;           float targetWidth,
;           int halign,
;           boolean wrap)

;https://javadoc.io/static/com.badlogicgames.gdx/gdx/1.11.0/com/badlogic/gdx/graphics/g2d/BitmapFontCache.html#addText-java.lang.CharSequence-float-float-int-int-float-int-boolean-java.lang.String-



; getting height/width of text with glyphlayout :::
;
; BitmapFont font;
; SpriteBatch spriteBatch;
; //... Load any font of your choice first
; FreeTypeFontGenerator fontGenerator = new FreeTypeFontGenerator(
;    Gdx.files.internal("myFont.ttf")
; );
; FreeTypeFontGenerator.FreeTypeFontParameter freeTypeFontParameter =
;       new FreeTypeFontGenerator.FreeTypeFontParameter();
; freeTypeFontParameter.size = size;
; fontGenerator.generateData(freeTypeFontParameter);
; font = fontGenerator.generateFont(freeTypeFontParameter);
;
; //Initialize the spriteBatch as requirement
;
; GlyphLayout glyphLayout = new GlyphLayout();
; String item = "Example";
; glyphLayout.setText(font,item);
; float w = glyphLayout.width;
; font.draw(spriteBatch, glyphLayout, (Game.SCREEN_WIDTH - w)/2, y);

