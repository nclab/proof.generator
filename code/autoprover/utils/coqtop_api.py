import subprocess
import os
import signal
import xml.etree.ElementTree as ET

def ignore_sigint():
    signal.signal(signal.SIGINT, signal.SIG_IGN)

class Coqtop():
    def __init__(self):
        try:
            self._coqtop = subprocess.Popen(
                    ['coqtop', '-debug', '-main-channel', 'stdfds', '-ideslave'],
                    # ['coqtop', '-main-channel', 'stdfds', '-ideslave'],
                    stdin = subprocess.PIPE,
                    stdout = subprocess.PIPE,
                    preexec_fn = ignore_sigint
                    )
        except OSError:
            print("Error: couldn't launch coqtop")

    def kill(self):
        if self.isRunning():
            try:
                self._coqtop.terminate()
            except OSError:
                pass
        self._coqtop = None

    def isRunning(self):
        return self._coqtop is not None

    def sendXML(self, xml):
        """ First, check wether the coq process is still running.
        Then, send the XML command, and finally wait for the response """
        if not self.isRunning():
            exit
        try:
            data=ET.tostring(xml, 'utf-8')
            # print(data)
            data = b'<call val="Query"><pair><string>Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).</string><state_id val="0"/></pair></call>'
            self._coqtop.stdin.write(data)
        except IOError:
            self.kill()
            return None

    def getResponse(self):
        acc = b''
        fd = self._coqtop.stdout.fileno()
        # os.set_blocking(fd, False)
        while True:
            try:
                acc += os.read(fd, 0x4000)
                try:
                    elt = ET.fromstring(acc)
                    return elt
                except ET.ParseError:
                    continue
            except OSError:
                return None

    def sendQuery(self, data):
        xml = ET.Element('call')
        xml.set('val', 'interp')
        xml.set('id', '14')
        xml.set('raw', 'true')
        xml.set('verbose', '')
        # xml.text = data.decode('utf-8')
        xml.text = data
        return self.sendXML(xml)

if __name__ == "__main__":
    coq = Coqtop()
    coq.sendQuery("asdas")
    coq._coqtop.stdin.close()
    print(coq.getResponse())
    coq.kill()
