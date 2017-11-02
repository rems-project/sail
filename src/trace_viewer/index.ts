import {remote} from "electron"
import fs = require("fs")
const dialog = remote.dialog
const app = remote.app

let topCallDiv = document.createElement("div")

const max_arg_length = 5000

abstract class Event {
    caller: Call

    protected div: HTMLDivElement | null = null

    public hide(): void {
        if (this.div != null) {
            this.div.remove()
            this.div = null
        }        
    }

    protected abstract showText(text: HTMLParagraphElement): void

    public show(): HTMLDivElement {
        let callerDiv: HTMLDivElement = (this.caller != null) ? this.caller.show() : topCallDiv
        
        if (this.div != null) {
            return this.div
        } else {
            this.div = document.createElement("div")
            this.div.className = "tree"
            callerDiv.appendChild(this.div)
            let text = document.createElement("p")
            this.showText(text)
            this.div.appendChild(text)
            return this.div
        }          
    }
}

class Load extends Event {
    loc: string
    val: string

    constructor(loc: string, val: string) {
        super()
        this.loc = loc
        this.val = val
    }

    protected showText(text: HTMLParagraphElement): void {
        text.className = "load"
        text.insertAdjacentText('beforeend', this.loc + " " + this.val)        
    }
}

class Read extends Event {
    reg: string
    value: string

    constructor(reg: string, value: string) {
        super()
        this.reg = reg
        this.value = value
    }

    public showText(text: HTMLParagraphElement): void {
        text.className = "read"
        text.insertAdjacentText('beforeend', this.reg + " " + this.value)
    }
}

class Write extends Event {
    reg: string
    value: string

    constructor(reg: string, value: string) {
        super()
        this.reg = reg
        this.value = value
    }

    public showText(text: HTMLParagraphElement): void {
        text.className = "write"
        text.insertAdjacentText('beforeend', this.reg + " " + this.value)
    }
}

class Call {
    fn: string
    arg: string
    ret: string
    callees: (Call | Event)[] = []
    caller: Call

    private div: HTMLDivElement | null = null        

    private toggle: boolean = false
    private toggleImg: HTMLImageElement | null = null

    constructor(fn: string, arg: string, ret: string) {
        this.fn = fn
        this.arg = arg
        this.ret = ret
    }

    public expand() {
        if (this.caller != undefined) {
            this.caller.expand()
        }
        this.showChildren()
    }

    public iter(f: (call: Call) => void): void {
        f(this)
        this.callees.forEach((callee) => {
            if (callee instanceof Call) { callee.iter(f) }
        })

    }

    public show(): HTMLDivElement {
        let callerDiv: HTMLDivElement = (this.caller != null) ? this.caller.show() : topCallDiv

        if (this.div != null) {
            return this.div
        } else {
            this.div = document.createElement("div")
            this.div.className = "tree"
            callerDiv.appendChild(this.div)
            let text = document.createElement("p")
            text.className = "call"
            if (this.callees.length > 0) {
                this.toggleImg = document.createElement("img")
                this.toggleImg.src = "List-add.svg"
                this.toggleImg.addEventListener('click', () => {
                    if (this.toggle) {
                    this.hideChildren()
                    } else {
                        this.showChildren()
                    }
                })
                text.appendChild(this.toggleImg)
            }
            this.toggle = false
            let display_arg = this.arg
            if (this.arg.length > max_arg_length) {
                display_arg = this.arg.slice(0, max_arg_length)
            }
            let display_ret = this.ret
            if (this.ret.length > max_arg_length) {
                display_ret = this.ret.slice(0, max_arg_length)
            }

            text.insertAdjacentText('beforeend', this.fn + " " + display_arg + " -> " + display_ret)
            this.div.appendChild(text)
            return this.div
        }
    }

    public hide(): void {
        if (this.toggle == true) {
            this.hideChildren()
        }

        if (this.div != null) {
            this.div.remove()
            this.div = null
        }
        if (this.toggleImg != null) {
            this.toggleImg.remove()
            this.toggleImg = null
        }
    }

    public hideChildren(): void {
        this.callees.forEach(call => {
            call.hide()
        })

        if (this.toggleImg != null) {
            this.toggleImg.src = "List-add.svg"
            this.toggle = false
        } else {
            alert("this.toggleImg was null!")
        }
    }

    public showChildren(): void {
        this.callees.forEach(call => {
            call.show()
        });

        if (this.toggleImg != null) {
            this.toggleImg.src = "List-remove.svg"
            this.toggle = true
        } else {
            alert("this.toggleImg was null!")
        }
    }

    public appendChild(child: Call | Write | Read | Load): void {
        child.caller = this

        this.callees.push(child)
    }
}

document.addEventListener('DOMContentLoaded', () => {
    let rootCall = new Call("ROOT", "", "")
    topCallDiv.id = "root"
    document.getElementById("container")!.appendChild(topCallDiv)

    let commandInput = document.getElementById("command") as HTMLInputElement

    commandInput.addEventListener("keydown", (event) => {
        if(event.keyCode == 13) {
            let cmd = commandInput.value.split(" ")
            commandInput.value = ""

            if (cmd[0] == "function") {
                rootCall.iter((call) => {
                    if (call.fn == cmd[1]) { call.caller.expand() }
                })
            }
        }
    })

    let files = dialog.showOpenDialog(remote.getCurrentWindow(), {title: "Select log file", defaultPath: app.getAppPath()})

    if (files == [] || files == undefined) {
        dialog.showErrorBox("Error", "No file selected")
        app.exit(1)
    }

    fs.readFile(files[0], 'utf-8', (err, data) => {
        if (err) {
            dialog.showErrorBox("Error", "An error occurred when reading the log: " + err.message)
            app.exit(1)
        }

        let lines = data.split("\n")
        // let indents = lines.map(line => line.search(/[^\s]/) / 2)
        lines = lines.map(line => line.trim())

        let stack : Call[] = [rootCall]

        lines.forEach(line => {
            if (line.match(/^Call:/)) {
                let words = line.slice(6).split(" ")
                let call = new Call(words[0], words.slice(1).join(" "), "")
                if (stack.length > 0) {
                    stack[stack.length - 1].appendChild(call)
                }
                stack.push(call)
            } else if (line.match(/^Return:/)) {
                let call = stack.pop()
                if (call == undefined) {
                    alert("Unbalanced return")
                    app.exit(1)
                } else {
                    call.ret = line.slice(8)
                }
            } else if (line.match(/^Write:/)) {
                let words = line.slice(7).split(" ")
                let write = new Write(words[0], words.slice(1).join(" "))
                if (stack.length > 0) {
                    stack[stack.length - 1].appendChild(write)
                }
            } else if (line.match(/^Read:/)) {
                let words = line.slice(6).split(" ")
                let read = new Read(words[0], words.slice(1).join(" "))
                if (stack.length > 0) {
                    stack[stack.length - 1].appendChild(read)
                }
            } else if (line.match(/^Load:/)) {
                let words = line.slice(6).split(" ")
                let load = new Load(words[0], words[1])
                if (stack.length > 0) {
                    stack[stack.length - 1].appendChild(load)
                }
            }
        })

        rootCall.show()
    })
})