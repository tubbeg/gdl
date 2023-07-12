(ns gdx.image-bb-crop)


; in split folder :
; convert '*.png' -set filename:fn '%[basename]' -channel alpha -trim '%[filename:fn].png'

; add dashes:

; for  i in *_*;do mv $i ${i//"_"/"-"};done


;;;


; - crop all creatures (bodies) to visible bounding box
; https://libgdx.com/wiki/graphics/2d/pixmaps
; https://stackoverflow.com/questions/29451787/libgdx-textureregion-to-pixmap

; convert beetle_1.png -channel alpha -trim beetle_1_cropped.png


; * do not crop images , just calculate bounding boxes for creature width/height
; * and for creature rendering calculate center-offset

; TODO performance of doing this on every startup ? save images directyle ?
; I could cache somewhere the bounding-boxes also and calculate only once.

; https://www.reddit.com/r/ffmpeg/comments/yka3vh/is_there_a_way_to_crop_an_image_based_on_alpha/
; magick input.png -channel alpha -trim output.png

(comment
 (use 'game.media)
 (require '[utils.core :refer (find-first)])

 (let [sprite (gdx.graphics/get-sprite
               @#'game.media/heroes
               [0 0])
       texture-region (:texture sprite)
       texture-data  (.getTextureData (.getTexture texture-region))
       ]
   (if-not (.isPrepared texture-data)
     (.prepare texture-data)
     )
   (let [pixmap (.consumePixmap texture-data)
         alpha-at (fn [x y]
                    (.a (com.badlogic.gdx.graphics.Color. (.getPixel pixmap x y))))
         not-transparent? (fn [x y]
                            (not (zero? (alpha-at x y))))

         ; TODO start with RegionX / Y not 0 / -1
         ; check on some not 0/0 sprite
         x      (.getRegionX      texture-region)
         y      (.getRegionY      texture-region)
         width  (.getRegionWidth  texture-region)
         height (.getRegionHeight texture-region)

         left-bb (find-first (fn [x]
                               (find-first #(not-transparent? x %)
                                           (range y height)))
                             (range x width))
         top-bb (find-first (fn [y]
                              (find-first #(not-transparent? % y)
                                          (range x width)))
                            (range y height))
         right-bb (find-first (fn [x]
                                (find-first #(not-transparent? x %)
                                            (range y height)))
                              (range (- width 1) -1 -1))
         bottom-bb (find-first (fn [y]
                                 (find-first #(not-transparent? % y)
                                             (range width)))
                               (range (- height 1) -1 -1))
         width-bb (+ (- right-bb left-bb) 1)
         height-bb (+ (- bottom-bb top-bb) 1)
         ]
     {:x      left-bb
      :y      top-bb
      :width  width-bb
      :height height-bb
      :center-x (+ left-bb (/ width-bb  2))
      :center-y (+ top-bb  (/ height-bb 2))
      })))

; getRegionX
; getRegionY
; getRegionWidth
; getRegionHeight

; TODO dispose pixmap !


; public void drawPixmap(Pixmap pixmap,
;                       int x,
;                       int y,
;                       int srcx,
;                       int srcy,
;                       int srcWidth,
;                       int srcHeight)
