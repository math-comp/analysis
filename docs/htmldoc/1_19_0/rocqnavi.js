
function renderMarkdowns()
{
    const md = markdownit({
        html: true,
        highlight: function (str, lang) {
            if (lang && hljs.getLanguage(lang)) {
                try { return hljs.highlight(str, { language: lang }).value; }
                catch (__) {}
            }
            return '';
        }
    })
          .use(texmath, { engine: katex,
                          delimiters: 'dollars'} )
          .use(markdownitDeflist);
    const elements = document.querySelectorAll('.markdown,.md');
    for (let elem of elements) {
	      elem.innerHTML = md.render(elem.textContent);
    }
}

function showDarkmodeWidget()
{
    new Darkmode({
	      time: '0.1s',
	      label: '🌓',
    }).showWidget();
}

function setUpSavingDetails() {
    $('details').on('toggle', function(event) {
	      var id = $(this).attr('id')
	      var isOpen = $(this).attr('open')
	      window.localStorage.setItem('details-'+id, isOpen)
    })

    function setDetailOpenStatus(item) {
	      if (item.includes('details-')) {
	          var id = item.split('details-')[1];
	          var status = window.localStorage.getItem(item)
	          if (status == 'open') {
		            $("#"+CSS.escape(id)).attr('open',true)
	          }
	      }
    }

    $( document ).ready(function() {
	      for (var i = 0; i < localStorage.length; i++) {
	          setDetailOpenStatus(localStorage.key(i));
	      }
    });
}

function setUpGraphZoom() {
    // Zoom for Graphviz SVG
    document.querySelectorAll("div.graph svg").forEach(svg => {
        svgPanZoom(svg, {
            zoomEnabled: true,
            mouseWheelZoomEnabled: true,
            controlIconsEnabled: true,
            fit: true,
            center: true
        });
    });
};

function setUpPaneResize() {
    const MIN_WIDTH = 120;
    const MAX_WIDTH = 600;
    const root = document.documentElement;

    function makeResizable(resizer, cssVarName, sidebarSelector, invert) {
        if (!resizer) return;
        const sidebar = document.querySelector(sidebarSelector);
        let startX = 0;
        let startWidth = 0;

        function onPointerMove(event) {
            const delta = invert ? (startX - event.clientX) : (event.clientX - startX);
            const newWidth = Math.min(Math.max(startWidth + delta, MIN_WIDTH), MAX_WIDTH);
            root.style.setProperty(cssVarName, newWidth + 'px');
        }
        function onPointerUp(event) {
            resizer.classList.remove('resizing');
            document.body.style.userSelect = '';
            resizer.releasePointerCapture(event.pointerId);
            resizer.removeEventListener('pointermove', onPointerMove);
            resizer.removeEventListener('pointerup', onPointerUp);
        }
        resizer.addEventListener('pointerdown', function(event) {
            startX = event.clientX;
            startWidth = sidebar.getBoundingClientRect().width;
            resizer.classList.add('resizing');
            document.body.style.userSelect = 'none';
            resizer.setPointerCapture(event.pointerId);
            resizer.addEventListener('pointermove', onPointerMove);
            resizer.addEventListener('pointerup', onPointerUp);
        });
    }

    makeResizable(document.querySelector('.resizer-left'), '--sidebar-left-width', 'div.sidebar', false);
    makeResizable(document.querySelector('.resizer-right'), '--sidebar-right-width', 'div.sidebar-right', true);
}

function init()
{
    renderMarkdowns();
    showDarkmodeWidget();
    setUpSavingDetails();
    setUpGraphZoom();
    setUpPaneResize();
}
