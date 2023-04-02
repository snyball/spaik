(load html)

(test html
      (= (let ((img "funny"))
           (html (img :src (fmt "https://my.site/{img}.png") nil)))
         "<img src=\"https://my.site/funny.png\"></img>"))
